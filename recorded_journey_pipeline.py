#!/usr/bin/env python3
r"""
recorded_journey_pipeline.py - Recorded-journey pipeline (Learn -> Generate -> Run), one file
=============================================================================================

A separate pipeline next to the IMAGE pipeline. It never changes IMAGE pipeline files or
outputs (workflows/, locators/, pom/, features/, the engine, codegen_with_screenshots.js) and
does not depend on any patch to them. Needs Python 3.9+ (standard library only) and the QE
install's node_modules (playwright, @cucumber/cucumber, ts-node) and bundled Firefox.

  learn     Record a journey with the LEAN RECORDER (embedded below): a copy of the platform's
            codegen_with_screenshots.js that writes the lean raw log directly - the pipeline-safe
            cleanup is applied before writing (same rules as raw_log_prune.py; output verified
            identical, e.g. a 311 MB recording -> 6.5 MB), so there is no separate prune step.
            It also: reports each popup/toast once when it appears (not on every DOM change),
            records clicks on icon-only buttons (trash/edit icons were dropped), starts popup/toast
            detection on every page (it never started on newly loaded pages), masks password
            fields by input type, and accepts self-signed test certificates.
            -> <project>/raw_logs/app_json_<scenario>.json (+ _screens/)

  generate  Raw log -> runnable test, deterministic (no LLM): every recorded action becomes a
            step, plus checks for what the recording observed:
              Then I should see element "<css>" [with text "..."]   (tester's marks)
              Then I should see message "..."                      (popups, toasts, validation)
              Then I should be on "/route/*"                        (page changes)
            -> <project>/recorded_journey/<scenario>/
                 features/recorded_journey.feature  (Scenario Outline; test data in Examples)
                 locators.json, support/recorded_journey.steps.ts (own steps + runtime),
                 cucumber.js, tsconfig.json, report.json, testdata/files/ (upload files)

  run       Run a generated journey (Cucumber + Playwright Firefox) with its own config.
  all       learn, then generate.
  self-test Check the generator logic.

Examples (PowerShell):
  python recorded_journey_pipeline.py learn    --project C:\QE\QEScriptsGenerator\ps01 --scenario PS-02 --url https://<app>/
  python recorded_journey_pipeline.py generate --project C:\QE\QEScriptsGenerator\ps01 --scenario PS-02
  python recorded_journey_pipeline.py run      --project C:\QE\QEScriptsGenerator\ps01 --scenario PS-02 [--headless] [--base-url URL]

The console never prints recorded values (only counts and field names). Generated folders
contain recorded values in the Examples row: keep client ones local.
"""
import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urlparse

USER_ACTIONS = ("click", "input", "radio", "checkbox", "select_change", "hover")
HINT = {"input": "txt", "radio": "rdo", "checkbox": "chk", "hover": "hov", "select_change": "ddl", "click": "btn"}
GUID = re.compile(r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}")
TEXTY = ("label", "exact-text", "text")
# attribute strategies shared by many elements (validation flags, ARIA state): never identify one element
NOISE_ATTR = re.compile(r"^(data-(?!testid$|test-id$)[\w-]+|aria-(?!label$|labelledby$)[\w-]+)$")


# ---------------------------------------------------------------- pages (URL -> page name)
# Same rules as the IMAGE pipeline (codegen_to_json._build_url_page_map) so page names match.
_GENERIC_TOKENS = {"home", "index", "app", "main", "default", "root", "pages", "page"}
_SKIP_SEGMENTS = {"icn_react", "icnreact", "icnreactstatic", "reactstatic", "static", "callback", "oauth",
                  "auth", "redirect", "loading", "processing", "intermediate"}


def _dynamic(seg: str) -> bool:
    if seg.isdigit():
        return True
    if re.match(r"^[\d][\d\-_]*[\d]$", seg) and re.sub(r"[\-_]", "", seg).isdigit():
        return True
    return len(seg) <= 10 and bool(re.match(r"^[A-Za-z0-9]+$", seg)) and sum(c.isdigit() for c in seg) / len(seg) >= 0.6


def _segments(url: str) -> Tuple[str, ...]:
    p = urlparse(url or "")
    frag = (p.fragment or "").strip()
    route = frag if frag.strip("/") else (p.path or "/")
    return tuple(s for s in re.split(r"[/\\]", route) if s and not _dynamic(s) and s.lower() not in _SKIP_SEGMENTS)


def _page_name(segs) -> str:
    tokens: List[str] = []
    for seg in segs:
        for part in re.split(r"[^a-zA-Z0-9]+", seg):
            tokens += re.findall(r"[A-Z]+(?=[A-Z][a-z]|[0-9]|$)|[A-Z]?[a-z]+|[0-9]+", part) or ([part] if part else [])
    out: List[str] = []
    for t in (t.lower() for t in tokens if t):
        if t not in _GENERIC_TOKENS and t not in out:
            out.append(t)
    return "".join(t.capitalize() for t in out) + "Page" if out else "HomePage"


def url_page_map(urls) -> Dict[str, str]:
    url_segs, spa = {}, set()
    for u in urls:
        if u:
            url_segs[u] = _segments(u)
            if (urlparse(u).fragment or "").strip("/ "):
                spa.add(url_segs[u])
    kids = defaultdict(set)
    for segs in url_segs.values():
        for i in range(len(segs)):
            kids[segs[:i]].add(segs[:i + 1])
    tabs = {p for p, ks in kids.items() if p and len(ks) >= 3 and all(not kids.get(k) and k in spa for k in ks)}
    return {u: _page_name(s[:-1] if s[:-1] in tabs else s) for u, s in url_segs.items()}


# ---------------------------------------------------------------- controls
def robust_strategies(ev: Dict[str, Any]) -> List[Dict[str, str]]:
    """The event's own recorded strategies, minus ones that cannot identify this element after a
    reload (Kendo GUID ids, shared attributes, the generic text siblings share), stable ones first."""
    raw = [s for s in ev.get("strategies") or [] if isinstance(s, dict) and str(s.get("value") or "").strip()]
    if not raw and ev.get("selector"):
        raw = [{"type": "css", "value": ev["selector"]}]
    click_text = re.sub(r"\s+", " ", str(ev.get("text") or "")).strip().lower() if ev.get("type") == "click" else ""

    def generated(v):  # Kendo GUID ids, also CSS-escaped ("#\32 9164a61-..." = "#29164a61-...")
        return bool(GUID.search(re.sub(r"\\3([0-9]) ?", r"\1", v)))

    def specific(t, v):  # pins one element across reloads (positional paths do not)
        return not generated(v) and (t in ("id", "name", "data-testid", "data-test-id") or (t == "xpath" and "@id=" in v)
                                     or (t == "css" and ("#" in v or "[" in v)))

    def rank(s):
        t, v = str(s.get("type")), str(s.get("value"))
        order = {"id": 0, "name": 0, "data-testid": 0, "data-test-id": 0}
        if t in order:
            return 0
        if t == "xpath" and "@id=" in v:
            return 1
        if t == "css" and "#" in v:
            return 2
        if t in ("exact-text", "label", "role"):
            return 3  # survives layout changes; positional paths below do not
        if t == "xpath-absolute":
            return 4
        return 6 if t == "text" else 5

    kept, seen = [], set()
    has_specific = any(specific(str(s.get("type")), str(s.get("value"))) for s in raw)
    for s in raw:
        t, v = str(s.get("type")), str(s.get("value")).strip()
        if generated(v) or NOISE_ATTR.match(t):
            continue
        if click_text and t in TEXTY and v.lower() == click_text and has_specific:
            continue
        if t == "css" and has_specific and not specific(t, v):
            continue  # "input.k-input-inner": first match is some other field
        key = (t, v)
        if key not in seen:
            seen.add(key)
            kept.append({k: s[k] for k in ("type", "value", "role") if s.get(k)})
    return sorted(kept, key=rank) or [{k: s[k] for k in ("type", "value", "role") if s.get(k)} for s in raw]


def _pascal(s: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[^A-Za-z0-9]+", s) if p)


def _name_parts(name: str, underscores: bool = False) -> List[str]:
    """Meaningful parts of a field name: 'Form.Email', 'ctl00$Main$Grid1$ctl05$BirthDate$dateInput' (ASP.NET
    WebForms) or 'form:email' (JSF); generated parts (ctl05, GUIDs) are dropped."""
    parts = [p for p in re.split(r"[.$:_]" if underscores else r"[.$:]", name)
             if p and not re.fullmatch(r"(?i)ctl\d+", p) and not GUID.search(p)]
    return parts or [name]


def _snake(s: str) -> str:
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s)
    return re.sub(r"[^a-z0-9]+", "_", s.lower()).strip("_") or "value"


# ---------------------------------------------------------------- build
def build(raw: Dict[str, Any]) -> Dict[str, Any]:
    events = sorted(raw.get("events") or [], key=lambda e: e.get("step", 0))
    url_page = url_page_map({e.get("url") or "" for e in events})
    start_url = next((e["url"] for e in events if str(e.get("url") or "").startswith("http")), "")

    # keystroke runs of one field collapse to their last value
    actions: List[Dict[str, Any]] = []
    for e in (e for e in events if e.get("type") in USER_ACTIONS):
        prev = actions[-1] if actions else None
        if (prev and e.get("type") == "input" == prev.get("type") and e.get("fieldName")
                and e.get("fieldName") == prev.get("fieldName") and e.get("url") == prev.get("url")):
            actions[-1] = e
        else:
            actions.append(e)

    controls: Dict[str, Dict[str, Any]] = {}
    by_strats: Dict[Tuple, str] = {}
    data: Dict[str, str] = {}
    data_owner: Dict[str, str] = {}
    steps: List[Dict[str, Any]] = []
    skipped: List[Dict[str, Any]] = []
    generated_selects: List[str] = []

    def control_for(ev, page) -> Optional[str]:
        strats = robust_strategies(ev)
        if not strats:
            return None
        sig = (page, tuple((s["type"], s["value"]) for s in strats))
        if sig in by_strats:
            return by_strats[sig]
        tail = _pascal(".".join(_name_parts(str(ev.get("fieldName") or ev.get("label") or ev.get("text") or "Field"), True)[-3:]))[:60]
        if ev.get("type") == "radio":
            tail += re.sub(r"[^A-Za-z0-9]", "", str(ev.get("selectedLabel") or ev.get("value") or ""))[:20]
        base = f"{page}_{HINT.get(ev.get('type'), 'ctl')}_{tail or 'Field'}"
        alias, n = base, 2
        while alias in controls:
            alias, n = f"{base}{n}", n + 1
        controls[alias] = {"page": page, "type": ev.get("type"), "strategies": strats}
        by_strats[sig] = alias
        return alias

    def data_key(ev, alias, value: str) -> str:
        """One key per (field, recorded value): a field re-typed with another value (failed login,
        then retry) keeps both values, so the replay repeats what happened in order."""
        name = str(ev.get("fieldName") or ev.get("label") or alias.split("_", 2)[-1])
        key = _snake("_".join(_name_parts(name)[-2:]))[:50]
        k, n = key, 2
        while k in data_owner and (data_owner[k] != alias or data[k] != value):
            k, n = f"{key}_{n}", n + 1
        data_owner[k] = alias
        return k

    for e in actions:
        t, page = e.get("type"), url_page.get(e.get("url") or "", "HomePage")
        text = re.sub(r"\s+", " ", str(e.get("text") or "")).strip()
        step = {"page": page, "raw_step": e.get("step")}
        if t == "click" and GUID.fullmatch(text) and not any(
                str(x.get("type")) in ("id", "name", "data-test", "data-testid", "data-test-id") and not GUID.search(str(x.get("value")))
                for x in e.get("strategies") or []):
            # an element the app made and clicked itself (a download link named by a random id)
            skipped.append({"raw_step": e.get("step"), "type": t, "page": page, "reason": "app-generated element (random id, e.g. a download link)"})
            continue
        if t == "click" and (e.get("isDropdownOption") or e.get("isAutoSuggestOption")) and text:
            step.update(kind="option", text=text)  # Kendo rebuilds option lists on every open: pick by text
        else:
            alias = control_for(e, page)
            if not alias:
                if t == "click" and text:
                    step.update(kind="option", text=text)
                else:
                    skipped.append({"raw_step": e.get("step"), "type": t, "page": page, "reason": "no locator recorded"})
                    continue
            elif t in ("input", "select_change"):
                value = str(e.get("selectedText") or e.get("value") or "")
                key = data_key(e, alias, value)
                data[key] = value
                step.update(kind="fill" if t == "input" else "select", control=alias, key=key)
                if t == "select_change":
                    # remember where the chosen option sat: ids in option lists (account numbers) change per run
                    for o in e.get("availableOptions") or []:
                        if value in (str(o.get("text", "")).strip(), str(o.get("value", ""))) and isinstance(o.get("index"), int):
                            controls[alias].setdefault("options", {})[value] = o["index"]
                            break
                    if re.fullmatch(r"\d{4,}", value) or GUID.search(value):
                        generated_selects.append(key)
            elif t == "radio":
                step.update(kind="radio", control=alias)
            elif t == "checkbox":
                on = str(e.get("value", "")).lower() in ("checked", "true", "on", "1")
                step.update(kind="check" if on else "uncheck", control=alias)
            elif t == "hover":
                step.update(kind="hover", control=alias)
            else:
                step.update(kind="click", control=alias)
        steps.append(step)

    calendar = re.compile(r"(?i)calendar|datepicker|rcMView|rcCal|k-calendar|ui-datepicker|flatpickr|react-datepicker|mat-calendar")
    calendar_clicks = sum(1 for e in actions if e.get("type") == "click"
                          and any(calendar.search(str(x.get("value"))) for x in e.get("strategies") or []))
    checks, ignored = verification_checks(events, actions, url_page, start_url, data)
    # each check goes right after the last action recorded before it (exact, by raw step number)
    inserts: Dict[int, List[Tuple[int, Dict[str, Any]]]] = defaultdict(list)
    for raw_step, chk in checks:
        before = [i for i, s in enumerate(steps) if s["raw_step"] < raw_step]
        inserts[(max(before) + 1) if before else 0].append((raw_step, chk))
    for pos in sorted(inserts, reverse=True):
        steps[pos:pos] = [c for _, c in sorted(inserts[pos], key=lambda x: x[0])]

    return {"start_url": start_url, "controls": controls, "steps": steps, "data": data, "skipped": skipped,
            "recorded_actions": len(actions), "assertions": len(checks), "ignored": ignored,
            "checks_by_kind": dict(Counter(c["kind"] for _, c in checks)), "calendar_clicks": calendar_clicks,
            "generated_selects": generated_selects,
            # errors the tester saw while recording (and carried on): not a failure when they show again
            "expected_errors": sorted({re.sub(r"\s+", " ", str(e.get("label") or "")).strip()[:150] for e in events
                                       if e.get("type") in ("modal", "toast") and APP_ERROR.search(str(e.get("label") or ""))})}


# ---------------------------------------------------------------- verifications
# Text that changes between runs (ids, dates, emails): never asserted literally.
VOLATILE = re.compile(r"\d{3,}|[\w.+-]+@[\w-]+\.\w|\d{1,2}[/-]\d{1,2}[/-]\d{2,4}")
# Error pages/banners an app shows when something broke on its side (not field validation)
APP_ERROR = re.compile(r"(?i)error (has )?occurred|something went wrong|unexpected error|server error")
# Recorder popup/toast reports that are not messages: spinners, unnamed dialogs.
NOISE_MESSAGE = re.compile(r"(?i)^(dialog|modal|toast|alert|loading|processing|please\s+wait|busy|saving|submitting|working)\b|^\W*$")


def url_pattern(url: str) -> str:
    """Route of a URL with ids replaced by '*': '/Provider/*/Details' or '#/Patient/Basic' (query ignored)."""
    p = urlparse(url or "")
    frag = (p.fragment or "").split("?")[0]
    hash_route = bool(frag.strip("/"))
    segs = ["*" if _dynamic(s) or GUID.search(s) else s for s in (frag if hash_route else p.path or "/").split("/") if s]
    return ("#/" if hash_route else "/") + "/".join(segs)


def verification_checks(events, actions, url_page, start_url, data) -> Tuple[List[Tuple[int, Dict[str, Any]]], Dict[str, int]]:
    """Everything the recording observed besides the actions, as checks:
    human marks (element visible, and its text when stable), popups/toasts/validation messages
    that appeared, and page changes (also makes the replay wait for each page)."""
    mask = lambda s: re.sub(r"[\w.+-]+@[\w-]+\.[\w.]+", "<email>", re.sub(r"\d{6,}", "#", s))
    squash = lambda s: re.sub(r"\s+", " ", str(s or "")).strip()
    main_page = next((e.get("pageId") for e in actions if e.get("pageId") is not None), None)
    on_main = lambda e: e.get("pageId") in (None, main_page)
    action_steps = sorted(e.get("step", 0) for e in actions)
    gap = lambda st: sum(1 for a in action_steps if a < st)  # which pause between actions
    value_key = {}
    for k, v in data.items():
        value_key.setdefault(v, k)
    checks: List[Tuple[int, Dict[str, Any]]] = []
    ignored: Counter = Counter()

    # 1. human marks (any kind the recorder supports: verification, popup, mandatory, ...)
    seen_sel = set()
    for m in (e for e in events if e.get("type") == "human_mark"):
        mk = m.get("mark") or {}
        sel = str(mk.get("selector") or "").strip()
        sel = GUID.sub("", re.sub(r"#" + GUID.pattern + r"([\w-]+)", lambda g: f'[id$="{g.group(1)}"]', sel)).strip()
        page = url_page.get(m.get("url") or "", "HomePage")
        if not sel or ('"' in sel and "'" in sel) or (page, sel) in seen_sel:
            ignored["human marks without a usable selector or repeated"] += 1
            continue
        seen_sel.add((page, sel))
        value = squash(mk.get("value"))
        if value in value_key:
            text = f"<{value_key[value]}>"  # shows a test-data value: follows the Examples row
        else:
            text = value if value and len(value) <= 100 and not VOLATILE.search(value) else ""
        kind = str(mk.get("kind") or "verification")
        label = mask(squash(mk.get("label")))[:120]
        checks.append((m.get("step", 0), {"kind": "see", "selector": sel, "text": text, "page": page,
                                          "label": label if kind == "verification" else f"({kind}) {label}"}))

    # 2. popups / toasts / validation messages: once per message per pause between actions
    seen_msg = set()
    for e in (e for e in events if e.get("type") in ("modal", "toast") and on_main(e)):
        text = squash(e.get("label"))
        cut = VOLATILE.search(text)
        text = text[:cut.start()].strip(" :-,(") if cut else text
        if NOISE_MESSAGE.search(text) or len(text) < 4:
            ignored["loading/unnamed/volatile popups"] += 1
            continue
        gp = gap(e.get("step", 0))
        if (gp, text.lower()) in seen_msg or (gp - 1, text.lower()) in seen_msg:
            seen_msg.add((gp, text.lower()))  # still showing since the previous action: not a new message
            ignored["repeated popup/toast reports"] += 1
            continue
        seen_msg.add((gp, text.lower()))
        checks.append((e.get("step", 0), {"kind": "message", "text": text[:80], "page": url_page.get(e.get("url") or "", "HomePage"),
                                          "label": f"{e.get('type')} appeared"}))

    # 3. page changes: the last navigation in each pause, when it lands on a different route
    # A navigation seconds after the previous one in the same pause had no recorded cause: the click
    # that caused it was lost (a link that navigates can unload the page before the recorder hears it).
    # Redirects follow within a fraction of a second and are just waited for.
    def ts(e):
        try:
            return datetime.fromisoformat(str(e.get("timestamp")).replace("Z", "+00:00")).timestamp()
        except ValueError:
            return None
    current, by_gap = url_pattern(start_url), defaultdict(list)
    for e in (e for e in events if e.get("type") == "navigation" and on_main(e) and str(e.get("url") or "").startswith("http")):
        if action_steps and e.get("step", 0) > action_steps[0]:
            by_gap[gap(e.get("step", 0))].append(e)
    for g in sorted(by_gap):
        chain = [[by_gap[g][0]]]
        for prev, e in zip(by_gap[g], by_gap[g][1:]):
            t0, t1 = ts(prev), ts(e)
            if t0 is not None and t1 is not None and t1 - t0 > 3:
                chain.append([e])  # a later, separate navigation
            else:
                chain[-1].append(e)  # redirect: keep waiting for where it lands
        for n, hops in enumerate(chain):
            e = hops[-1]
            pat = url_pattern(e["url"])
            if pat == current:
                ignored["navigations to the same route (reload/postback)"] += 1
                continue
            current = pat
            page = url_page.get(e["url"], "HomePage")
            if n and "*" in pat:
                # the target URL holds an id that differs per run: cannot open it directly
                ignored["page changes with no recorded click to a URL with ids (re-record that click)"] += 1
            if n and "*" not in pat:
                u = urlparse(e["url"])
                target = u.path + (f"?{u.query}" if u.query else "") + (f"#{u.fragment}" if u.fragment else "")
                checks.append((e.get("step", 0), {"kind": "goto", "url": target, "page": page,
                                                  "label": "navigation with no recorded click: open the page directly"}))
                continue
            checks.append((e.get("step", 0), {"kind": "url", "pattern": pat, "page": page, "label": ""}))
    return checks, dict(ignored)


# ---------------------------------------------------------------- data checks
_SUSPECT = [
    (re.compile(r"\d_|_\d"), "mask placeholder '_' left in value (recorded mid-typing)"),
    (re.compile(r"(?i)(?:^|[/\-.])(?:year|month|day|yyyy|mm|dd)(?:$|[/\-.])"), "mask placeholder text (year/month/day)"),
    (re.compile(r"^\d{1,2}/(?:\d{1,2}/)?\d{1,3}$"), "date with an incomplete year (recorded mid-typing)"),
    (re.compile(r"^\*{3,}$"), "masked in the raw log: set the real value"),
]


def suspect_values(data: Dict[str, str]) -> List[Dict[str, str]]:
    out = []
    for k, v in data.items():
        if not v.strip():
            out.append({"where": k, "reason": "empty value"})
            continue
        for rx, reason in _SUSPECT:
            if rx.search(v):
                out.append({"where": k, "reason": reason})
                break
    return out


# ---------------------------------------------------------------- render
def _q(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _cell(s: str) -> str:
    # ponytail: a value containing '"' would need cucumber-side unescaping; rare in form data
    return s.replace("\\", "\\\\").replace("|", "\\|").replace("\n", " ")


def render_feature(name: str, plan: Dict[str, Any]) -> str:
    lines = [f"@recorded-journey", f"Feature: Recorded journey - {name}",
             "  Replays the recorded user actions in order (generated by recorded_journey_pipeline.py, no LLM).", "",
             f"  Scenario Outline: Recorded journey {name}", "    Given I open the recorded app"]
    page, prev_then, first = None, False, True
    for s in plan["steps"]:
        if s["page"] != page:
            page = s["page"]
            lines.append(f"    # --- {page} ---")
        k = s["kind"]
        if k == "goto":
            lines.append(f"    # Note: {s['label']}")
            lines.append(f"    When I open the page {_q(s['url'])}")
            prev_then = False
            continue
        if k in ("see", "message", "url"):
            if s.get("label"):
                lines.append(f"    # Verify: {s['label']}")
            if k == "see":
                sel = f"'{s['selector']}'" if '"' in s["selector"] else _q(s["selector"])
                text = f"I should see element {sel}" + (f" with text {_q(s['text'])}" if s.get("text") else "")
            elif k == "message":
                text = f"I should see message {_q(s['text'])}"
            else:
                text = f"I should be on {_q(s['pattern'])}"
            lines.append(f"    {'And' if prev_then else 'Then'} {text}")
            prev_then = True
            continue
        kw = "When" if prev_then or first else "And"
        prev_then = first = False
        text = {
            "fill": lambda: f'I fill "<{s.get("key")}>" into {_q(s.get("control", ""))}',
            "select": lambda: f'I select "<{s.get("key")}>" in {_q(s.get("control", ""))}',
            "option": lambda: f"I pick option {_q(s.get('text', ''))}",
            "radio": lambda: f"I choose radio {_q(s.get('control', ''))}",
            "check": lambda: f"I check {_q(s.get('control', ''))}",
            "uncheck": lambda: f"I uncheck {_q(s.get('control', ''))}",
            "hover": lambda: f"I hover over {_q(s.get('control', ''))}",
            "click": lambda: f"I click {_q(s.get('control', ''))}",
        }[k]()
        lines.append(f"    {kw} {text}")
    keys = list(plan["data"]) or ["none"]
    vals = [plan["data"].get(k, "") for k in keys]
    lines += ["", "    Examples:", "      | " + " | ".join(keys) + " |",
              "      | " + " | ".join(_cell(v) for v in vals) + " |", ""]
    return "\n".join(lines)


CUCUMBER_JS = """module.exports = {
  default: {
    paths: ["features/**/*.feature"],
    require: ["support/**/*.ts"],
    requireModule: ["ts-node/register"],
    format: ["progress", "json:reports/cucumber.json"],
    order: "defined"
  }
};
"""

TSCONFIG = """{
  "compilerOptions": { "target": "es2020", "module": "commonjs", "moduleResolution": "node", "esModuleInterop": true, "skipLibCheck": true, "strict": false },
  "ts-node": { "transpileOnly": true }
}
"""

STEPS_TS = r'''// Generated by recorded_journey_pipeline.py - self-contained: does not use the engine's BasePage/generic steps.
import { Before, After, Given, When, Then, setDefaultTimeout } from "@cucumber/cucumber";
import { firefox, Browser, Page, Locator } from "playwright";
import * as fs from "fs";
import * as path from "path";

setDefaultTimeout(90 * 1000);
type Strategy = { type: string; value: string; role?: string };
const ROOT = path.resolve(__dirname, "..");
const LOC: { start_url: string; controls: Record<string, { page: string; strategies: Strategy[] }> } =
  JSON.parse(fs.readFileSync(path.join(ROOT, "locators.json"), "utf-8"));

let browser: Browser | undefined;
let page: Page;
let lastSuggest: { loc: Locator; value: string } | undefined;
// Popup / toast / validation texts that became visible since the last action (toasts vanish fast).
const seen: string[] = [];
const squash = (s: string) => String(s || "").replace(/\s+/g, "").toLowerCase();
const MESSAGE_SEL = '[role="dialog"],[role="alertdialog"],[role="alert"],[role="status"],.modal.show,.toast,.k-notification,' +
  '.k-window,.k-dialog,.alert,.notification,.snackbar,.validation-summary-errors,.field-validation-error,.k-tooltip-validation';
const COLLECTOR = `(() => {
  let shown = new Set(), timer;
  const vis = (el) => el.checkVisibility ? el.checkVisibility() : !!el.offsetParent;
  const scan = () => {
    const now = new Set();
    document.querySelectorAll(${JSON.stringify(MESSAGE_SEL)}).forEach((el) => {
      const t = (el.textContent || "").trim();
      if (!t || !vis(el)) return;
      now.add(t);
      if (!shown.has(t)) { try { window.__rjSeen(t.slice(0, 4000)); } catch (e) {} }
    });
    shown = now;
  };
  new MutationObserver(() => { clearTimeout(timer); timer = setTimeout(scan, 150); })
    .observe(document, { childList: true, subtree: true, characterData: true, attributes: true, attributeFilter: ["class", "style", "aria-hidden"] });
})();`;
const newAction = () => { seen.length = 0; };
// "{unique}" in a test value becomes a short id that is new on every run (one-time data: usernames, emails)
const RUN_ID = Date.now().toString(36).slice(-6);
const v = (s: string) => String(s).replace(/\{unique\}/g, RUN_ID);
// A test never hands off to another app: phone/email/sms links would open a browser dialog that blocks the page.
const NO_EXTERNAL_LINKS = `document.addEventListener("click", (e) => {
  const a = e.target && e.target.closest && e.target.closest('a[href^="tel:"], a[href^="mailto:"], a[href^="sms:"]');
  if (a) { e.preventDefault(); console.log("[replay] external link not opened: " + a.getAttribute("href").split(":")[0]); }
}, true);`;

Before(async function () {
  browser = await firefox.launch({ headless: /^(1|true|yes)$/i.test(process.env.HEADLESS || "") });
  const context = await browser.newContext({ viewport: { width: 1366, height: 900 }, ignoreHTTPSErrors: true });
  await context.exposeBinding("__rjSeen", (_src, t: string) => { seen.push(String(t)); });
  await context.addInitScript(COLLECTOR);
  await context.addInitScript(NO_EXTERNAL_LINKS);
  page = await context.newPage();
});

// App-error guard: a visible "an error occurred" / "something went wrong" banner means the app failed,
// even when every click still worked. Errors also seen while recording are allowed. Opt out: RJ_ALLOW_APP_ERRORS=1.
const APP_ERROR = /error (has )?occurred|something went wrong|unexpected error|server error/i;
async function assertNoAppError() {
  if (/^(1|true|yes)$/i.test(process.env.RJ_ALLOW_APP_ERRORS || "")) return;
  const found: string = await page.evaluate((src) => {
    const rx = new RegExp(src, "i");
    const w = document.createTreeWalker(document.body || document.documentElement, NodeFilter.SHOW_TEXT);
    let n: Node | null;
    while ((n = w.nextNode())) {
      const t = (n.textContent || "").trim();
      const el = n.parentElement as any;
      if (t && t.length < 300 && rx.test(t) && el && (el.checkVisibility ? el.checkVisibility() : el.offsetParent)) return t.replace(/\s+/g, " ");
    }
    return "";
  }, APP_ERROR.source).catch(() => "");
  if (!found) return;
  const allowed: string[] = (LOC as any).expected_errors || [];
  if (allowed.some((e) => squash(found).includes(squash(e)) || squash(e).includes(squash(found)))) return;
  throw new Error(`The app showed an error: "${found.slice(0, 150)}" (seen before this step; set RJ_ALLOW_APP_ERRORS=1 to ignore)`);
}

After(async function (scenario) {
  if (String(scenario.result?.status) !== "FAILED") {
    await page.waitForTimeout(1000);
    await assertNoAppError();  // an error after the last step fails the scenario too
  }
  if (String(scenario.result?.status) === "FAILED") {
    fs.mkdirSync(path.join(ROOT, "reports"), { recursive: true });
    await page.screenshot({ path: path.join(ROOT, "reports", "failure.png"), fullPage: true }).catch(() => {});
  }
  await browser?.close();
});

const q = (v: string) => v.replace(/\\/g, "\\\\").replace(/"/g, '\\"');

function resolve(s: Strategy): Locator {
  const v = String(s.value);
  switch (s.type) {
    case "id": return page.locator(`[id="${q(v)}"]`);
    case "name": return page.locator(`[name="${q(v)}"]`);
    case "role": return page.getByRole((s.role || "textbox") as any, { name: v });
    case "label": return page.getByLabel(v);
    case "placeholder": return page.getByPlaceholder(v);
    case "title": return page.getByTitle(v);
    case "text": return page.getByText(v);
    case "exact-text": return page.getByText(v, { exact: true });
    case "xpath": case "xpath-absolute": return page.locator(`xpath=${v}`);
    case "data-testid": case "data-test-id": return page.getByTestId(v);
    case "css": return page.locator(v);
    default:
      if (/^(aria-[\w-]+|data-[\w-]+|for|alt|href|src|value|type)$/.test(s.type)) return page.locator(`[${s.type}="${q(v)}"]`);
      return page.locator(v);
  }
}

// Try the control's strategies in order (stable ids first) until one performs the action.
async function act(key: string, what: string, fn: (l: Locator) => Promise<unknown>) {
  const ctl = LOC.controls[key];
  if (!ctl) throw new Error(`No control "${key}" in locators.json`);
  newAction();
  await page.waitForLoadState("domcontentloaded").catch(() => {});
  await assertNoAppError();
  await page.waitForLoadState("networkidle", { timeout: 2000 }).catch(() => {});  // apps that poll never go idle
  const errors: string[] = [];
  for (let i = 0; i < ctl.strategies.length; i++) {
    const s = ctl.strategies[i];
    try {
      const all = resolve(s);
      await all.first().waitFor({ state: "attached", timeout: i === 0 ? 8000 : 1500 });
      // several matches (a "Next" per wizard panel): take the visible one; hidden styled inputs still work
      const visible = all.filter({ visible: true }).first();
      const loc = (await visible.count()) ? visible : all.first();
      await fn(loc);
      if (i > 0) console.log(`  [${what}] ${key}: worked with strategy ${i + 1} (${s.type})`);
      return;
    } catch (e: any) {
      errors.push(`${i + 1}. ${s.type}: ${String(e?.message ?? e).split("\n")[0]}`);
    }
  }
  throw new Error(`${what} failed for "${key}" (page ${ctl.page}):\n  ` + errors.join("\n  "));
}

function uploadPath(value: string): string {
  const name = value.split(/[\\/]/).pop() || value;
  const hit = [value, path.join(ROOT, "testdata", "files", name)].find(p => { try { return fs.statSync(p).isFile(); } catch { return false; } });
  if (!hit) throw new Error(`Upload file not found: put "${name}" in ${path.join(ROOT, "testdata", "files")}`);
  return hit;
}

async function fill(loc: Locator, value: string) {
  if (await loc.evaluate((el: any) => el?.tagName === "INPUT" && el?.type === "file")) return loc.setInputFiles(uploadPath(value), { timeout: 10000 });
  // Autocomplete / masked / date inputs react to key events only; fill() bypasses them.
  const keyed = await loc.evaluate((el: any) =>
    el?.getAttribute("role") === "combobox" || el?.hasAttribute("aria-autocomplete") ||
    ["autocomplete", "combobox", "multicolumncombobox", "dateinput", "maskedtextbox", "datepicker", "datetimepicker", "timepicker"].includes(el?.getAttribute("data-role") || "") ||
    !!el?.closest?.(".k-autocomplete, .k-combobox, .k-multiselect, .k-dropdowngrid, .k-dateinput, .k-maskedtextbox, .k-datepicker, .k-datetimepicker"));
  if (keyed) {
    await loc.fill("", { timeout: 10000 });
    await loc.pressSequentially(value, { delay: 80, timeout: 30000 });
    lastSuggest = { loc, value };
    return;
  }
  await loc.fill(value, { timeout: 10000 });
}

async function click(loc: Locator) {
  // A recorded click on a disabled control (locked wizard tab) had no effect: wait ~3 s, then skip it.
  const disabled = async () => !(await loc.isEnabled().catch(() => true)) || (await loc.getAttribute("aria-disabled").catch(() => null)) === "true";
  if (await loc.isVisible().catch(() => false) && await disabled()) {
    for (let t = 0; t < 6 && await disabled(); t++) await page.waitForTimeout(500);
    if (await disabled()) { console.warn("  [click] target disabled; skipped (no effect when recorded either)"); return; }
  }
  await loc.click({ timeout: 10000 });
}

async function selectOption(l: Locator, key: string, value: string) {
  try { await l.selectOption({ label: value }, { timeout: 3000 }); return; } catch {}
  try { await l.selectOption(value, { timeout: 1000 }); return; } catch {}
  // the recorded option is gone (an id that changes per run, e.g. a new account number): same position
  const idx = (LOC.controls[key] as any)?.options?.[value];
  if (typeof idx !== "number" || idx >= await l.locator("option").count()) throw new Error(`option "${value}" is not in the list`);
  await l.selectOption({ index: idx }, { timeout: 3000 });
  console.warn(`  [select] "${value}" not in the list (changes per run): picked option ${idx + 1} as recorded`);
}

async function setChecked(loc: Locator, on: boolean) {
  // Styled radios/checkboxes hide the real input; users click its label.
  if (!(await loc.isVisible().catch(() => false))) {
    const id = await loc.getAttribute("id").catch(() => null);
    const label = id ? page.locator(`label[for="${q(id)}"]`).filter({ visible: true }).first() : null;
    if (label && await label.count() && (await loc.isChecked().catch(() => null)) !== on) return label.click({ timeout: 10000 });
    return on ? loc.check({ force: true, timeout: 10000 }) : loc.uncheck({ force: true, timeout: 10000 });
  }
  return on ? loc.check({ timeout: 10000 }) : loc.uncheck({ timeout: 10000 });
}

async function pickOption(text: string) {
  newAction();
  await assertNoAppError();
  const exact = new RegExp(`^\\s*${text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*$`);
  const options = page.locator('li.k-item, .k-list-item, [role="option"], [role="menuitem"]').filter({ hasText: exact });
  const shown = options.filter({ visible: true }).first();
  const appears = (ms: number) => shown.waitFor({ state: "visible", timeout: ms }).then(() => true).catch(() => false);
  // Kendo closes popups on scroll/blur, which a real click can cause: dispatch to the seen element if needed.
  const pick = async () => {
    const el = await shown.elementHandle({ timeout: 1000 });
    try { await shown.click({ timeout: 3000 }); }
    catch { console.warn(`  [option] "${text}" hidden before click; dispatching click`); await el!.dispatchEvent("click"); }
  };
  if (await appears(3000)) return pick();
  // List not open (async search, or closed again): retype the last suggest input, or ArrowDown.
  const focused = page.locator("input:focus, textarea:focus").first();
  const typed = await focused.inputValue({ timeout: 1000 }).catch(() => "");
  const target = typed ? { loc: focused, value: typed } : lastSuggest;
  if (target) {
    await target.loc.fill("").catch(() => {});
    await target.loc.pressSequentially(target.value, { delay: 80 }).catch(() => {});
  } else if (await options.count()) {
    await page.keyboard.press("ArrowDown").catch(() => {});
  }
  if (await appears(8000)) return pick();
  await page.getByText(text, { exact: true }).filter({ visible: true }).first().click({ timeout: 10000 });
}

async function seeElement(selector: string): Promise<Locator> {
  // ASP.NET ids with dots read as id+class in CSS; recorded paths are positional (nth-of-type).
  const literalIds = selector.replace(/#([A-Za-z][\w-]*(?:\.[\w-]+)+)/g, (_m, id) => `[id="${id}"]`);
  const unpositioned = literalIds.replace(/:nth-(?:of-type|child)\(\d+\)/g, "");
  const candidates = [...new Set([selector, literalIds, unpositioned])];
  let last: any;
  for (const sel of candidates) {
    const loc = page.locator(sel).filter({ visible: true }).first();
    try { await loc.waitFor({ state: "visible", timeout: 15000 / candidates.length }); return loc; }
    catch (e) { last = e; }
  }
  throw last;
}

async function seeElementText(selector: string, text: string) {
  const loc = await seeElement(selector);
  const want = squash(text);
  let got = "";
  for (let t = 0; t < 20; t++) {  // text can arrive after the element (async data)
    got = await loc.evaluate((el: any) => `${el.innerText || el.textContent || ""} ${el.value ?? ""}`).catch(() => "");
    if (squash(got).includes(want)) return;
    await page.waitForTimeout(250);
  }
  throw new Error(`Element "${selector}" is visible but does not show "${text}" (shows "${got.trim().slice(0, 120)}")`);
}

async function seeMessage(text: string) {
  const want = squash(text);
  const deadline = Date.now() + 15000;
  while (Date.now() < deadline) {
    if (seen.some((s) => squash(s).includes(want))) return;
    const now = await page.evaluate((sel) => {
      const vis = (el: any) => el.checkVisibility ? el.checkVisibility() : !!el.offsetParent;
      return [...document.querySelectorAll(sel)].filter(vis).map((el) => el.textContent || "").join(" ") + " " + (document.body?.innerText || "");
    }, MESSAGE_SEL).catch(() => "");
    if (squash(now).includes(want)) return;
    await page.waitForTimeout(300);
  }
  throw new Error(`Message not shown within 15 s: "${text}"`);
}

async function onRoute(pattern: string) {
  const hash = pattern.startsWith("#");
  const body = pattern.replace(/^#/, "").replace(/^\/+|\/+$/g, "");
  const rx = new RegExp("(^|/)" + body.split("/").map((s) => s === "*" ? "[^/]+" : s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("/") + "/?$", "i");
  const ok = (u: URL) => {
    const route = hash ? u.hash.replace(/^#/, "").split("?")[0] : u.pathname;
    return body ? rx.test(route) : /^\/?$/.test(route);
  };
  try { await page.waitForURL(ok, { timeout: 30000, waitUntil: "domcontentloaded" }); }
  catch { throw new Error(`Expected to be on "${pattern}" but the page is ${new URL(page.url()).pathname}${new URL(page.url()).hash}`); }
}

Given("I open the recorded app", async () => {
  await page.goto(process.env.BASE_URL || LOC.start_url, { waitUntil: "load", timeout: 60000 });
});
When("I fill {string} into {string}", (value: string, key: string) => act(key, "fill", l => fill(l, v(value))));
When("I select {string} in {string}", (value: string, key: string) => act(key, "select", l => selectOption(l, key, value)));
When("I click {string}", (key: string) => act(key, "click", click));
When("I pick option {string}", (text: string) => pickOption(text));
When("I choose radio {string}", (key: string) => act(key, "radio", l => setChecked(l, true)));
When("I check {string}", (key: string) => act(key, "check", l => setChecked(l, true)));
When("I uncheck {string}", (key: string) => act(key, "uncheck", l => setChecked(l, false)));
When("I hover over {string}", (key: string) => act(key, "hover", l => l.hover({ timeout: 10000 })));
Then("I should see element {string}", async (selector: string) => { await seeElement(selector); });
Then("I should see element {string} with text {string}", (selector: string, text: string) => seeElementText(selector, v(text)));
Then("I should see message {string}", (text: string) => seeMessage(v(text)));
Then("I should be on {string}", (pattern: string) => onRoute(pattern));
When("I open the page {string}", async (target: string) => {
  newAction();
  await page.goto(new URL(target, process.env.BASE_URL || LOC.start_url).href, { waitUntil: "load", timeout: 60000 });
});
'''


# ================================================================ LEARN (lean recorder)
# The lean recorder below is the platform's codegen_with_screenshots.js with three changes (marked in it):
# the pipeline-safe cleanup is applied before the raw log is written (LEAN_JS, the same rules as
# raw_log_prune.py, output verified identical), each dialog/toast is reported once when it appears,
# and passwords are masked unless --keep-passwords. The IMAGE pipeline's recorder file is not touched.
LEAN_JS = r'''// ===== Lean raw log: the pipeline-safe cleanup applied before writing (same rules as raw_log_prune.py) =====
// Keeps everything the IMAGE pipeline and the recorded-journey generator read; drops the redundant
// copies (learn_enriched.flattened, per-step top-level dom_metadata, duplicate fields/messages,
// strategy lists inside field maps) and masks password values unless --keep-passwords is given.
const LEAN_FIELD_META_KEEP = ["key", "selector", "tag", "input_type", "role", "label", "normalized_label", "visible",
  "hidden", "required", "readonly", "field_type", "value", "dynamic"];
const leanIsObj = (v) => v !== null && typeof v === "object" && !Array.isArray(v);
const leanDefined = (o) => Object.keys(o).filter((k) => o[k] !== undefined);   // in-memory objects can hold undefined
const leanHas = (o, k) => k in o && o[k] !== undefined;
const leanOr = (v) => (v === undefined || v === null || v === "" || v === 0 || v === false ? "" : String(v));
const leanFmt = (o, k) => (leanHas(o, k) ? (o[k] === null ? "None" : String(o[k])) : "");

function leanDedupe(items, keys) {
  if (!Array.isArray(items) || !items.length) return [];
  const seen = new Set(), out = [];
  for (const it of items) {
    if (!leanIsObj(it)) continue;
    const id = keys.map((k) => leanOr(it[k])).join("|");
    if (seen.has(id)) continue;
    seen.add(id);
    out.push(it);
  }
  return out;
}

function leanFieldMap(fm) {
  const out = {};
  for (const k of leanDefined(fm)) {
    const v = fm[k];
    if (leanIsObj(v)) {
      const s = {};
      for (const f of LEAN_FIELD_META_KEEP) if (leanHas(v, f)) s[f] = v[f];
      out[k] = s;
    } else out[k] = v;
  }
  return out;
}

function leanEntry(e) {
  if (!leanIsObj(e)) return e;
  if (leanHas(e, "snapshotStep")) {
    const s = {};
    for (const k of ["snapshotStep", "url", "locationPathname", "documentTitle", "reason", "label"]) if (leanHas(e, k)) s[k] = e[k];
    if (leanHas(e, "pageMessages")) s.pageMessages = e.pageMessages;
    for (const k of ["display_fields", "readonly_fields", "mandatory_fields", "popups", "messages", "inline_errors"]) {
      const v = e[k];
      if (Array.isArray(v) && v.length) {
        s[k] = ["display_fields", "readonly_fields", "mandatory_fields"].includes(k) ? leanDedupe(v, ["key", "selector"])
          : ["popups", "messages"].includes(k) ? leanDedupe(v, ["selector", "messageText"]) : v;
      }
    }
    if (leanIsObj(e.dom_metadata) && leanDefined(e.dom_metadata).length) s.dom_metadata = leanFieldMap(e.dom_metadata);
    return s;
  }
  const keys = leanDefined(e);
  if (keys.length && keys.every((k) => leanIsObj(e[k]))) return leanFieldMap(e);
  const s = {};
  for (const k of ["selector", "key", "label", "type", "fieldType", "value", "readonly", "mandatory", "display", "text", "normalized_text"])
    if (leanHas(e, k)) s[k] = e[k];
  return s;
}

function leanSnapshots(snaps) {
  return snaps.map((snap) => {
    if (!leanIsObj(snap)) return snap;
    const n = Object.assign({}, snap);
    const once = (list, a, b) => {
      const seen = new Set();
      return list.filter((x) => leanIsObj(x)).filter((x) => {
        const key = `${leanFmt(x, a)}|${leanFmt(x, b)}`;
        if (seen.has(key)) return false;
        seen.add(key);
        return true;
      });
    };
    if (Array.isArray(snap.display_fields) && snap.display_fields.length) n.display_fields = once(snap.display_fields, "key", "selector");
    if (Array.isArray(snap.messages) && snap.messages.length) n.messages = once(snap.messages, "selector", "messageText");
    if (Array.isArray(snap.popups) && snap.popups.length) n.popups = once(snap.popups, "selector", "messageText");
    return n;
  });
}

const LEAN_PASSWORD_NAME = /passw|pwd|passcode|passphrase/i;
function leanMaskPasswords(node) {
  if (Array.isArray(node)) { node.forEach(leanMaskPasswords); return; }
  if (!leanIsObj(node)) return;
  const name = ["fieldName", "key", "name", "normalized_label"].map((k) => leanOr(node[k])).join(" ");
  const type = String(node.input_type || node.inputType || "").toLowerCase();
  const v = node.value;
  if ((type === "password" || LEAN_PASSWORD_NAME.test(name)) && !(v === undefined || v === null || v === "" || v === "****")) node.value = "****";
  for (const k of Object.keys(node)) leanMaskPasswords(node[k]);
}

function leanRawLog(data, maskPasswords) {
  const r = {};
  r.events = data.events || [];
  if (leanHas(data, "actions")) r.actions = data.actions;
  if (leanHas(data, "navigation_events")) r.navigation_events = data.navigation_events;
  r.display_fields = leanDedupe(data.display_fields, ["key", "selector"]);
  r.mandatory_fields = leanDedupe(data.mandatory_fields, ["key", "selector"]);
  r.readonly_fields = leanDedupe(data.readonly_fields, ["key", "selector"]);
  r.messages = leanDedupe(data.messages, ["selector", "messageText"]);
  r.popups = leanDedupe(data.popups, ["selector", "messageText"]);
  r.inline_errors = data.inline_errors || [];
  const first = (data.dom_metadata || []).find((e) => leanIsObj(e) && leanDefined(e).length);
  r.dom_metadata = first ? [leanEntry(first)] : [];
  r.human_marked_verifications = data.human_marked_verifications || [];
  const le = data.learn_enriched;
  if (leanIsObj(le) && leanDefined(le).length) {
    const rl = {};
    const dm = Array.isArray(le.dom_metadata) ? le.dom_metadata : [];
    rl.dom_metadata = dm.length ? leanSnapshots(dm.filter(leanIsObj).map(leanEntry)) : [];
    if (leanHas(le, "human_marks")) rl.human_marks = le.human_marks;
    for (const k of ["navigation_events", "actions"]) if (leanHas(le, k)) rl[k] = le[k];
    r.learn_enriched = rl;
  }
  if (maskPasswords) leanMaskPasswords(r);
  return r;
}
'''

RECORDER_JS = r'''#!/usr/bin/env node

// Enhanced Playwright manual recorder (Learn Mode) that:
//  - Accepts --project and --scenario (and optional --url)
//  - Launches a firefox browser for manual interaction
//  - Records user actions + navigation as JSON events:
//      <project>/raw_logs/app_json_<scenario>.json
//  - Captures screenshots alongside the events into:
//      <project>/raw_logs/app_json_<scenario>_screens/step_XXX_*.png
//
// Enhancements:
//  - Captures rich DOM metadata per snap: labels, readonly, required, hidden/visible,
//    computed/display-only fields, data constraints, inferred field types, dynamic presence.
//  - Captures popup/message semantics: modals, toasts, inline errors, banners, success msgs.
//  - Captures human intent via hotkeys + context menu + floating panel:
//      Shift+Click, DoubleClick, RightClick menu, Marking mode toggle.
//  - Stores into backward-compatible JSON with new top-level Learn fields
//    and learn_enriched block.
//
// One manual run => JSON log + screenshots (no separate codegen run required).
//
// LEAN RECORDER (recorded_journey_pipeline.py): copy of codegen_with_screenshots.js that
//  - writes the lean raw log directly (pipeline-safe cleanup applied before writing; no prune step),
//  - reports each dialog/toast once when it appears (not on every DOM change while it stays open),
//  - masks password values unless --keep-passwords, and accepts self-signed test certificates.
// The IMAGE pipeline's own recorder is not changed.

const { firefox } = require('playwright');
const fs = require('fs');
const path = require('path');

function parseArgs(argv) {
  const args = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a.startsWith('--')) {
      const key = a.slice(2);
      const next = argv[i + 1];
      if (next && !next.startsWith('--')) {
        args[key] = next;
        i++;
      } else {
        args[key] = true;
      }
    }
  }
  return args;
}

/*__LEAN_RAW_LOG__*/

(async () => {
  const args = parseArgs(process.argv.slice(2));
  const project = args.project || 'banking_app';
  const scenario = args.scenario || 's001';
  const baseUrl = args.url || 'http://localhost:3000';

  const projectRoot = path.resolve(process.cwd(), project);
  const rawLogsDir = path.join(projectRoot, 'raw_logs');
  const jsonFile = path.join(rawLogsDir, `app_json_${scenario}.json`);
  const screensDir = path.join(rawLogsDir, `app_json_${scenario}_screens`);
  fs.mkdirSync(screensDir, { recursive: true });

  console.log(`[info] Project root: ${projectRoot}`);
  console.log(`[info] Screenshots dir: ${screensDir}`);
  console.log(`[info] JSON log file: ${jsonFile}`);

  let browser;
  let context;
  let page;  // kept for backward compatibility
  let snapIndex = 1;
  let step = 1;
  const events = [];

  // ========== MULTI-PAGE TRACKING ==========
  // Track all open pages and which one is currently active
  const allPages = [];
  let activePage = null;
  let pageCounter = 0;  // For unique page IDs

  // Rich Learn snapshots (one per snap).
  const domSnapshots = [];

  // Human intent marks gathered from in-page UX
  const humanMarks = {
    verification_marks: [],
    popup_marks: [],
    mandatory_marks: [],
    business_rule_marks: [],
    navigation_marks: []
  };

  let finished = false;

  // ========== FINALIZE FUNCTION (must be defined early for page close handler) ==========
  async function finalize(reason) {
    if (finished) return;
    finished = true;
    try {
      fs.mkdirSync(rawLogsDir, { recursive: true });

      // Flattened Learn fields for new pipeline stages
      const flattened = {
        dom_metadata: domSnapshots.map(s => s.dom_metadata),
        display_fields: domSnapshots.flatMap(s => s.display_fields || []),
        readonly_fields: domSnapshots.flatMap(s => s.readonly_fields || []),
        mandatory_fields: domSnapshots.flatMap(s => s.mandatory_fields || []),
        popups: domSnapshots.flatMap(s => s.popups || []),
        inline_errors: domSnapshots.flatMap(s => s.inline_errors || []),
        messages: domSnapshots.flatMap(s => s.messages || []),
        human_marked_verifications: humanMarks.verification_marks,
        navigation_events: events.filter(e => e.type === 'navigation'),
        actions: events.filter(e => e.type !== 'navigation')
      };

      const payload = {
        // Backward compatible core
        events,

        // New top-level Learn enriched fields (as requested)
        ...flattened,

        // Also keep a structured block for enriched consumers
        learn_enriched: {
          dom_metadata: domSnapshots,
          human_marks: humanMarks,
          flattened
        }
      };

      const lean = leanRawLog(payload, !args['keep-passwords']);
      fs.writeFileSync(jsonFile, JSON.stringify(lean, null, 2), 'utf-8');
      console.log(`[info] Saved lean JSON log with ${events.length} events to ${jsonFile} [reason=${reason}]`);
    } catch (e) {
      console.error('[error] Failed to save JSON log:', e.message || e);
    }
  }

  // ========== HELPER: Get current active page for operations ==========
  function getCurrentPage() {
    return activePage || page;
  }

  async function snap(reason, label, eventPayload) {
    const currentPage = getCurrentPage();
    if (!currentPage) return;

    const safeLabel = (label || reason || 'snap')
      .toString()
      .replace(/[^a-zA-Z0-9]+/g, '_')
      .slice(0, 40) || 'snap';

    const fileName = `step_${String(step).padStart(3, '0')}_${safeLabel}.png`;
    const filePath = path.join(screensDir, fileName);

    try {
      // LEAN RECORDER: what the user sees (full-page captures of long pages are unreadable and big);
      // --full-page-screenshots restores the old behaviour.
      await currentPage.screenshot({ path: filePath, fullPage: !!args['full-page-screenshots'] });

      const event = Object.assign(
        {
          reason,
          label: safeLabel,
          screenshot: `app_json_${scenario}_screens/${fileName}`,
          step,
          timestamp: new Date().toISOString(),
          url: currentPage.url()
        },
        eventPayload || {}
      );
      events.push(event);

      // Capture a cheap-but-rich DOM snapshot for Learn-enriched consumers.
      try {
        const snapshot = await currentPage.evaluate((ev) => {
          const doc = document;
          const url = ev && ev.url ? ev.url : window.location.href;
          const title = doc.title || '';
          const pathname = window.location.pathname || '';

          // ---------- helpers ----------
          const isVisible = (el) => {
            if (!el) return false;
            const style = window.getComputedStyle(el);
            if (style.display === 'none' || style.visibility === 'hidden' || style.opacity === '0')
              return false;
            const rect = el.getBoundingClientRect();
            return rect.width > 0 && rect.height > 0;
          };

          const norm = (s) =>
            (s || '')
              .toString()
              .trim()
              .replace(/\s+/g, ' ')
              .toLowerCase();

          const normalizeKey = (s) =>
            norm(s)
              .replace(/[^a-z0-9]+/g, '_')
              .replace(/^_+|_+$/g, '')
              .slice(0, 60);

          const getLabelFor = (el) => {
            if (!el) return '';
            const aria = el.getAttribute('aria-label') || el.getAttribute('aria-labelledby');
            if (aria) {
              if (aria.includes(' ')) {
                // aria-labelledby list
                const ids = aria.split(/\s+/);
                const texts = ids.map(id => {
                  const n = doc.getElementById(id);
                  return n ? (n.textContent || '').trim() : '';
                }).filter(Boolean);
                if (texts.length) return texts.join(' ');
              } else {
                const n = doc.getElementById(aria);
                if (n && n.textContent) return n.textContent.trim();
              }
              return aria;
            }

            const id = el.id;
            if (id) {
              const lbl = doc.querySelector(`label[for="${CSS.escape(id)}"]`);
              if (lbl && lbl.textContent) return lbl.textContent.trim();
            }

            // closest label
            const closestLabel = el.closest('label');
            if (closestLabel && closestLabel.textContent) return closestLabel.textContent.trim();

            // placeholder fallback
            const ph = el.getAttribute('placeholder');
            if (ph) return ph.trim();

            // sibling / parent text heuristic
            const parent = el.parentElement;
            if (parent) {
              const sibText = Array.from(parent.childNodes)
                .filter(n => n !== el && n.nodeType === Node.TEXT_NODE)
                .map(n => (n.textContent || '').trim())
                .join(' ');
              if (sibText) return sibText.trim();
            }

            return '';
          };

          const inferFieldType = (el) => {
            const tag = (el.tagName || '').toLowerCase();
            const typeAttr = (el.getAttribute('type') || '').toLowerCase();
            const role = (el.getAttribute('role') || '').toLowerCase();
            const inputMode = (el.getAttribute('inputmode') || '').toLowerCase();

            if (tag === 'select' || role === 'listbox') return 'dropdown';
            if (typeAttr === 'checkbox' || role === 'checkbox') return 'checkbox';
            if (typeAttr === 'radio' || role === 'radio') return 'radio';
            if (tag === 'textarea') return 'textarea';
            if (typeAttr === 'date') return 'date';
            if (typeAttr === 'datetime-local') return 'datetime';
            if (typeAttr === 'number' || inputMode === 'numeric') return 'number';

            const name = norm(el.name || el.id || getLabelFor(el));
            if (/amount|currency|price|rs|usd|inr|eur/.test(name)) return 'currency';
            if (/date|dob|day|month|year/.test(name)) return 'date';

            return 'text';
          };

          const cssPath = (el) => {
            try {
              if (!el || !(el instanceof Element)) return null;
              const parts = [];
              let node = el;
              while (node && node.nodeType === 1 && parts.length < 6) {
                let part = node.nodeName.toLowerCase();
                if (node.id) {
                  part += `#${node.id}`;
                  parts.unshift(part);
                  break;
                } else {
                  const cls = (node.className || '').toString().trim().split(/\s+/).filter(Boolean);
                  if (cls.length) part += `.${cls.slice(0, 2).join('.')}`;
                  const parent = node.parentElement;
                  if (parent) {
                    const siblings = Array.from(parent.children).filter(c => c.nodeName === node.nodeName);
                    if (siblings.length > 1) {
                      const idx = siblings.indexOf(node) + 1;
                      part += `:nth-of-type(${idx})`;
                    }
                  }
                }
                parts.unshift(part);
                node = node.parentElement;
              }
              return parts.join(' > ');
            } catch {
              return null;
            }
          };

          // ---------- locator strategy capture (compact; mirrors clientSideScript) ----------
          const isUnstableValue = (v) => {
            if (!v) return true;
            const s = String(v).trim();
            if (!s) return true;
            if (/^:r[0-9a-z]+:$/i.test(s)) return true;
            if (/^mui-\d+$/i.test(s)) return true;
            if (/^(css|emotion|sc)-[a-z0-9]{4,}$/i.test(s)) return true;
            if (/^[a-f0-9]{8,}$/i.test(s)) return true;
            if (/^[a-z0-9]{1,3}-[a-z0-9]{6,}$/i.test(s)) return true;
            return false;
          };
          const implicitRole = (el) => {
            const tag = (el.tagName || '').toLowerCase();
            const type = (el.getAttribute('type') || '').toLowerCase();
            if (tag === 'button') return 'button';
            if (tag === 'a' && el.hasAttribute('href')) return 'link';
            if (tag === 'select') return 'combobox';
            if (tag === 'textarea') return 'textbox';
            if (tag === 'input') {
              if (type === 'submit' || type === 'button' || type === 'reset') return 'button';
              if (type === 'checkbox') return 'checkbox';
              if (type === 'radio') return 'radio';
              if (['text','email','tel','url','search','password','number',''].includes(type)) return 'textbox';
            }
            return '';
          };
          const absXPath = (el) => {
            try {
              if (!el || el.nodeType !== 1) return null;
              const parts = [];
              let node = el;
              while (node && node.nodeType === 1 && node !== doc.documentElement) {
                const tag = node.nodeName.toLowerCase();
                let idx = 1; let sib = node.previousElementSibling;
                while (sib) { if (sib.nodeName === node.nodeName) idx++; sib = sib.previousElementSibling; }
                parts.unshift(`${tag}[${idx}]`);
                node = node.parentElement;
              }
              return '/html/' + parts.join('/');
            } catch { return null; }
          };
          const anchoredXPaths = (el) => {
            const found = [];
            try {
              const tail = [];
              let node = el;
              while (node && node.nodeType === 1 && node !== doc.documentElement) {
                const tag = node.nodeName.toLowerCase();
                let idx = 1; let sib = node.previousElementSibling;
                while (sib) { if (sib.nodeName === node.nodeName) idx++; sib = sib.previousElementSibling; }
                if (node !== el) {
                  const atid = node.getAttribute('data-testid') || node.getAttribute('data-test-id');
                  const aid = node.getAttribute('id');
                  if (atid && !isUnstableValue(atid)) found.push({ attr: 'data-testid', val: atid, tail: tail.slice() });
                  else if (aid && !isUnstableValue(aid)) found.push({ attr: 'id', val: aid, tail: tail.slice() });
                }
                tail.unshift(`${tag}[${idx}]`);
                node = node.parentElement;
              }
            } catch { /* ignore */ }
            return found.slice(0, 2).map(a => ({
              value: `//*[@${a.attr}=${JSON.stringify(a.val)}]` + (a.tail.length ? '/' + a.tail.join('/') : ''),
              anchor: a.val,
            }));
          };
          const collectRawStrategies = (el) => {
            const list = [];
            if (!el || el.nodeType !== 1) return list;
            const tag = (el.tagName || '').toLowerCase();
            const push = (type, value, extra) => {
              if (value === null || value === undefined) return;
              const v = String(value).trim();
              if (!v) return;
              const entry = { type, value: v };
              if (extra && extra.role) entry.role = extra.role;
              if (extra && extra.anchor) entry.anchor = extra.anchor;
              if (extra && extra.unstable) entry.unstable = true;
              list.push(entry);
            };
            const TEST_HOOKS = ['data-testid','data-test-id','data-test','data-qa','data-cy'];
            for (const a of TEST_HOOKS) {
              const val = el.getAttribute(a);
              if (val) push(a, val, { unstable: isUnstableValue(val) });
            }
            if (el.id) push('id', el.id, { unstable: isUnstableValue(el.id) });
            if (el.getAttribute('name')) push('name', el.getAttribute('name'));
            if (el.getAttribute('for')) push('for', el.getAttribute('for'));
            for (const attr of Array.from(el.attributes || [])) {
              if (attr.name.startsWith('data-') && !TEST_HOOKS.includes(attr.name)) {
                push(attr.name, attr.value, { unstable: isUnstableValue(attr.value) });
              }
            }
            for (const attr of Array.from(el.attributes || [])) {
              if (!attr.name.startsWith('aria-')) continue;
              if (attr.name === 'aria-labelledby') {
                const texts = attr.value.split(/\s+/).map(id => {
                  const n = doc.getElementById(id);
                  return n ? (n.textContent || '').trim() : '';
                }).filter(Boolean);
                if (texts.length) push('aria-labelledby', texts.join(' '));
              } else {
                push(attr.name, attr.value);
              }
            }
            const role = el.getAttribute('role') || implicitRole(el);
            const accName = getLabelFor(el) || (el.innerText || el.textContent || '').trim();
            if (role && accName) push('role', accName, { role });
            if (el.getAttribute('title')) push('title', el.getAttribute('title'));
            if (el.getAttribute('alt')) push('alt', el.getAttribute('alt'));
            const labelText = getLabelFor(el);
            if (labelText) push('label', labelText);
            if (el.getAttribute('placeholder')) push('placeholder', el.getAttribute('placeholder'));
            const text = (el.innerText || el.textContent || '').trim().replace(/\s+/g, ' ');
            if (text && text.length <= 120) { push('exact-text', text); push('text', text); }
            // `value` intentionally not captured — mutable state, not a locator.
            if (el.id && !isUnstableValue(el.id)) push('css', `#${CSS.escape(el.id)}`);
            const cls = (el.className || '').toString().trim().split(/\s+/)
              .filter(Boolean).filter(c => !isUnstableValue(c));
            if (cls.length) push('css', `${tag}.${cls.slice(0, 3).map(c => CSS.escape(c)).join('.')}`);
            if (el.getAttribute('name')) push('css', `${tag}[name=${JSON.stringify(el.getAttribute('name'))}]`);
            const cp = cssPath(el);
            if (cp) push('css', cp);
            for (const ax of anchoredXPaths(el)) push('xpath', ax.value, { anchor: ax.anchor });
            const abs = absXPath(el);
            if (abs) push('xpath-absolute', abs);
            return list;
          };
          const STRATEGY_TIERS = {
            'data-testid': 100, 'data-test-id': 100, 'data-test': 100, 'data-qa': 100, 'data-cy': 100,
            'id': 90, 'role': 70,
            'aria-label': 65, 'aria-labelledby': 65, 'label': 65, 'for': 65,
            'name': 60, 'placeholder': 60, 'title': 60, 'alt': 60,
            'exact-text': 52, 'text': 50, 'xpath': 40, 'css': 30, 'xpath-absolute': 10,
          };
          const strategyTier = (type) => {
            if (type in STRATEGY_TIERS) return STRATEGY_TIERS[type];
            if (type.startsWith('data-')) return 80;
            if (type.startsWith('aria-')) return 45;
            return 20;
          };
          const rankStrategies = (rawList) => (rawList || [])
            .map((s, i) => ({ s, i, score: strategyTier(s.type) - (s.unstable ? 35 : 0) }))
            .sort((a, b) => (b.score - a.score) || (a.i - b.i))
            .map(x => x.s);

          // ---------- fields ----------
          const controls = Array.from(
            doc.querySelectorAll('input, select, textarea, [role="textbox"], [role="combobox"], [role="listbox"]')
          );

          const mandatory_fields = [];
          const readonly_fields = [];
          const display_fields = [];
          const dom_metadata = {};

          controls.slice(0, 500).forEach((el) => {
            const visible = isVisible(el);
            const labelText = getLabelFor(el);
            const key =
              normalizeKey(el.name || el.id || labelText || el.getAttribute('aria-label') || el.getAttribute('role') || 'field');

            const required =
              el.hasAttribute('required') ||
              el.getAttribute('aria-required') === 'true' ||
              /\*$/.test((labelText || '').trim());

            const readonly =
              el.hasAttribute('readonly') ||
              el.hasAttribute('disabled') ||
              el.getAttribute('aria-readonly') === 'true';

            const meta = {
              key,
              selector: cssPath(el),
              tag: (el.tagName || '').toLowerCase(),
              input_type: (el.getAttribute('type') || '').toLowerCase() || null,
              role: el.getAttribute('role') || null,
              label: labelText || null,
              normalized_label: norm(labelText),
              visible,
              hidden: !visible,
              required,
              readonly,
              pattern: el.getAttribute('pattern') || null,
              min: el.getAttribute('min') || null,
              max: el.getAttribute('max') || null,
              maxlength: el.getAttribute('maxlength') || null,
              field_type: inferFieldType(el),
              value: (el.value || '').toString().slice(0, 200) || null,
              strategies: rankStrategies(collectRawStrategies(el)),
              dynamic: false // set by consumer by diffing steps
            };

            dom_metadata[key] = meta;

            if (readonly) readonly_fields.push(meta);
            if (required) mandatory_fields.push(meta);
          });

          // display-only / computed values
          const displayNodes = Array.from(
            doc.querySelectorAll('span, div, p, td, th, [data-display], [data-testid], [role="status"]')
          ).filter(isVisible);

          displayNodes.slice(0, 500).forEach((n) => {
            const txt = (n.textContent || '').trim();
            if (!txt) return;

            // avoid capturing massive layout text
            if (txt.length > 200) return;

            const key = normalizeKey(n.getAttribute('data-testid') || n.id || txt.slice(0, 40));
            display_fields.push({
              key,
              selector: cssPath(n),
              text: txt,
              normalized_text: norm(txt),
              source: 'dom',
              visible: true
            });
          });

          // ---------- popups/messages ----------
          const popups = [];
          const inline_errors = [];
          const messages = [];

          const addMessage = (type, severity, node, text, source = 'learn') => {
            if (!text) return;
            const entry = {
              selector: cssPath(node),
              type,                 // modal / toast / banner / inline_error / validation / success
              severity,             // error / warning / confirmation / validation / info / success
              messageText: text.slice(0, 250),
              source
            };
            messages.push(entry);
            if (type === 'modal' || type === 'toast' || type === 'banner') popups.push(entry);
            if (type === 'inline_error' || type === 'validation') inline_errors.push(entry);
          };

          // modals/dialogs
          const dialogNodes = doc.querySelectorAll(
            '[role="dialog"], [role="alertdialog"], .modal.show, .modal[aria-hidden="false"], [aria-modal="true"]'
          );
          dialogNodes.forEach((d) => {
            const text = (d.textContent || '').trim();
            if (text) addMessage('modal', 'confirmation', d, text);
          });

          // toasts & alerts
          const toastNodes = doc.querySelectorAll(
            '[role="alert"], .toast.show, .toast:not(.hide), .notification, .snackbar'
          );
          toastNodes.forEach((t) => {
            const text = (t.textContent || '').trim();
            if (text) addMessage('toast', 'info', t, text);
          });

          // inline errors
          const errorNodes = doc.querySelectorAll(
            '.error, .invalid-feedback, .field-error, .has-error, [aria-invalid="true"]'
          );
          errorNodes.forEach((e) => {
            const text = (e.textContent || '').trim();
            if (text) addMessage('inline_error', 'validation', e, text);
          });

          // banners
          const bannerNodes = doc.querySelectorAll(
            '.banner-error, .banner-warning, .alert-danger, .alert-warning, .alert-success'
          );
          bannerNodes.forEach((b) => {
            const text = (b.textContent || '').trim();
            if (!text) return;
            let sev = 'info';
            const cls = (b.className || '').toString().toLowerCase();
            if (cls.includes('error') || cls.includes('danger')) sev = 'error';
            else if (cls.includes('warning')) sev = 'warning';
            else if (cls.includes('success')) sev = 'success';
            addMessage('banner', sev, b, text);
          });

          return {
            snapshotStep: ev && typeof ev.step === 'number' ? ev.step : null,
            url,
            reason: ev && ev.reason,
            label: ev && ev.label,
            documentTitle: title,
            locationPathname: pathname,

            dom_metadata,
            display_fields,
            readonly_fields,
            mandatory_fields,
            popups,
            inline_errors,
            messages
          };
        }, event);

        domSnapshots.push(snapshot);
      } catch (e) {
        // Best-effort only; do not block recorder on DOM snapshot errors.
        console.warn('[warn] DOM snapshot failed:', e.message || e);
      }

      step += 1;
      snapIndex += 1;
      console.log(`[snap] ${reason} -> ${path.relative(process.cwd(), filePath)}`);
    } catch (e) {
      console.warn('[warn] Failed to take screenshot:', e.message || e);
    }
  }

  // ========== CLIENT-SIDE SCRIPT (shared across all pages) ==========
  // This is the script injected into each page for event capture
  const clientSideScript = () => {
    function safeCall(fn) { try { fn(); } catch { /* ignore */ } }

    function debounce(fn, delay) {
      let t;
      return (...args) => {
        clearTimeout(t);
        t = setTimeout(() => safeCall(() => fn(...args)), delay);
      };
    }

    // basic CSS path generator for marks
    function cssPath(el) {
      try {
        if (!el || !(el instanceof Element)) return null;
        const parts = [];
        let node = el;
        while (node && node.nodeType === 1 && parts.length < 6) {
          let part = node.nodeName.toLowerCase();
          if (node.id) {
            part += `#${node.id}`;
            parts.unshift(part);
            break;
          } else {
            const cls = (node.className || '').toString().trim().split(/\s+/).filter(Boolean);
            if (cls.length) part += `.${cls.slice(0, 2).join('.')}`;
            const parent = node.parentElement;
            if (parent) {
              const siblings = Array.from(parent.children).filter(c => c.nodeName === node.nodeName);
              if (siblings.length > 1) {
                const idx = siblings.indexOf(node) + 1;
                part += `:nth-of-type(${idx})`;
              }
            }
          }
          parts.unshift(part);
          node = node.parentElement;
        }
        return parts.join(' > ');
      } catch {
        return null;
      }
    }

    function getLabel(el) {
      if (!el) return '';
      const aria = el.getAttribute('aria-label');
      if (aria) return aria;
      if (el.id) {
        const lbl = document.querySelector(`label[for="${CSS.escape(el.id)}"]`);
        if (lbl) return (lbl.textContent || '').trim();
      }
      const closestLabel = el.closest('label');
      if (closestLabel) return (closestLabel.textContent || '').trim();
      return (el.getAttribute('placeholder') || el.innerText || el.textContent || '').trim();
    }

    // ===== Locator strategy capture (exhaustive + priority-ranked) =====
    // Framework-generated values (MUI/React/emotion) are captured but flagged
    // `unstable` so ranking demotes them rather than losing the information.
    function isUnstableValue(v) {
      if (!v) return true;
      const s = String(v).trim();
      if (!s) return true;
      if (/^:r[0-9a-z]+:$/i.test(s)) return true;        // React useId  :r1:
      if (/^mui-\d+$/i.test(s)) return true;             // MUI auto id
      if (/^(css|emotion|sc)-[a-z0-9]{4,}$/i.test(s)) return true; // emotion/styled
      if (/^[a-f0-9]{8,}$/i.test(s)) return true;        // long hex hashes
      if (/^[a-z0-9]{1,3}-[a-z0-9]{6,}$/i.test(s)) return true;    // generic hashed
      return false;
    }

    function implicitRole(el) {
      const tag = el.tagName.toLowerCase();
      const type = (el.getAttribute('type') || '').toLowerCase();
      if (tag === 'button') return 'button';
      if (tag === 'a' && el.hasAttribute('href')) return 'link';
      if (tag === 'select') return 'combobox';
      if (tag === 'textarea') return 'textbox';
      if (tag === 'img') return 'img';
      if (/^h[1-6]$/.test(tag)) return 'heading';
      if (tag === 'input') {
        if (type === 'submit' || type === 'button' || type === 'reset') return 'button';
        if (type === 'checkbox') return 'checkbox';
        if (type === 'radio') return 'radio';
        if (type === 'range') return 'slider';
        if (['text', 'email', 'tel', 'url', 'search', 'password', 'number', ''].includes(type)) return 'textbox';
      }
      return '';
    }

    function accessibleNameFor(el) {
      const aria = el.getAttribute('aria-label');
      if (aria && aria.trim()) return aria.trim();
      const labelledBy = el.getAttribute('aria-labelledby');
      if (labelledBy) {
        const texts = labelledBy.split(/\s+/).map(id => {
          const n = document.getElementById(id);
          return n ? (n.textContent || '').trim() : '';
        }).filter(Boolean);
        if (texts.length) return texts.join(' ');
      }
      const lbl = getLabel(el);
      if (lbl) return lbl;
      return (el.innerText || el.textContent || '').trim();
    }

    // Absolute /html/tag[n]/... path — unique but brittle, last-resort only.
    function absXPath(el) {
      try {
        if (!el || el.nodeType !== 1) return null;
        const parts = [];
        let node = el;
        while (node && node.nodeType === 1 && node !== document.documentElement) {
          const tag = node.nodeName.toLowerCase();
          let idx = 1;
          let sib = node.previousElementSibling;
          while (sib) {
            if (sib.nodeName === node.nodeName) idx++;
            sib = sib.previousElementSibling;
          }
          parts.unshift(`${tag}[${idx}]`);
          node = node.parentElement;
        }
        return '/html/' + parts.join('/');
      } catch {
        return null;
      }
    }

    // Anchored relative xpaths: //*[@id="anchor"]/relative/tail — far less brittle
    // than the absolute path because only the tail below the anchor must hold.
    function anchoredXPaths(el) {
      const found = [];
      try {
        const tail = [];
        let node = el;
        while (node && node.nodeType === 1 && node !== document.documentElement) {
          const tag = node.nodeName.toLowerCase();
          let idx = 1;
          let sib = node.previousElementSibling;
          while (sib) {
            if (sib.nodeName === node.nodeName) idx++;
            sib = sib.previousElementSibling;
          }
          if (node !== el) {
            const atid = node.getAttribute('data-testid') || node.getAttribute('data-test-id');
            const aid = node.getAttribute('id');
            if (atid && !isUnstableValue(atid)) {
              found.push({ attr: 'data-testid', val: atid, tail: tail.slice() });
            } else if (aid && !isUnstableValue(aid)) {
              found.push({ attr: 'id', val: aid, tail: tail.slice() });
            }
          }
          tail.unshift(`${tag}[${idx}]`);
          node = node.parentElement;
        }
      } catch { /* ignore */ }
      return found.slice(0, 2).map(a => ({
        value: `//*[@${a.attr}=${JSON.stringify(a.val)}]` + (a.tail.length ? '/' + a.tail.join('/') : ''),
        anchor: a.val,
      }));
    }

    // Capture every locator candidate derivable from the element (unranked).
    function collectRawStrategies(el) {
      const list = [];
      if (!el || el.nodeType !== 1) return list;
      const tag = el.tagName.toLowerCase();
      const push = (type, value, extra) => {
        if (value === null || value === undefined) return;
        const v = String(value).trim();
        if (!v) return;
        const entry = { type, value: v };
        if (extra && extra.role) entry.role = extra.role;
        if (extra && extra.anchor) entry.anchor = extra.anchor;
        if (extra && extra.unstable) entry.unstable = true;
        list.push(entry);
      };
      const TEST_HOOKS = ['data-testid', 'data-test-id', 'data-test', 'data-qa', 'data-cy'];

      // test hooks
      for (const a of TEST_HOOKS) {
        const val = el.getAttribute(a);
        if (val) push(a, val, { unstable: isUnstableValue(val) });
      }
      // identity
      if (el.id) push('id', el.id, { unstable: isUnstableValue(el.id) });
      if (el.getAttribute('name')) push('name', el.getAttribute('name'));
      if (el.getAttribute('for')) push('for', el.getAttribute('for'));
      // every other data-* attribute (open-ended)
      for (const attr of Array.from(el.attributes || [])) {
        if (attr.name.startsWith('data-') && !TEST_HOOKS.includes(attr.name)) {
          push(attr.name, attr.value, { unstable: isUnstableValue(attr.value) });
        }
      }
      // every aria-* attribute
      for (const attr of Array.from(el.attributes || [])) {
        if (!attr.name.startsWith('aria-')) continue;
        if (attr.name === 'aria-labelledby') {
          const texts = attr.value.split(/\s+/).map(id => {
            const n = document.getElementById(id);
            return n ? (n.textContent || '').trim() : '';
          }).filter(Boolean);
          if (texts.length) push('aria-labelledby', texts.join(' '));
        } else {
          push(attr.name, attr.value);
        }
      }
      // role + accessible name
      const role = el.getAttribute('role') || implicitRole(el);
      const accName = accessibleNameFor(el);
      if (role && accName) push('role', accName, { role });
      // title / alt
      if (el.getAttribute('title')) push('title', el.getAttribute('title'));
      if (el.getAttribute('alt')) push('alt', el.getAttribute('alt'));
      // label / placeholder
      const labelText = getLabel(el);
      if (labelText) push('label', labelText);
      if (el.getAttribute('placeholder')) push('placeholder', el.getAttribute('placeholder'));
      // text content
      const text = (el.innerText || el.textContent || '').trim().replace(/\s+/g, ' ');
      if (text && text.length <= 120) {
        push('exact-text', text);
        push('text', text);
      }
      // NOTE: element `value` is intentionally NOT captured — it is mutable
      // element state, not a way to locate the element, and per-keystroke
      // input events would otherwise flood the list with partial values.
      // css selectors
      if (el.id && !isUnstableValue(el.id)) push('css', `#${CSS.escape(el.id)}`);
      const cls = (el.className || '').toString().trim().split(/\s+/)
        .filter(Boolean).filter(c => !isUnstableValue(c));
      if (cls.length) push('css', `${tag}.${cls.slice(0, 3).map(c => CSS.escape(c)).join('.')}`);
      if (el.getAttribute('name')) push('css', `${tag}[name=${JSON.stringify(el.getAttribute('name'))}]`);
      const cp = cssPath(el);
      if (cp) push('css', cp);
      // xpath
      for (const ax of anchoredXPaths(el)) push('xpath', ax.value, { anchor: ax.anchor });
      const abs = absXPath(el);
      if (abs) push('xpath-absolute', abs);

      return list;
    }

    // Fixed priority tiers — higher score is tried first by BasePage's retry loop.
    const STRATEGY_TIERS = {
      'data-testid': 100, 'data-test-id': 100, 'data-test': 100, 'data-qa': 100, 'data-cy': 100,
      'id': 90,
      'role': 70,
      'aria-label': 65, 'aria-labelledby': 65, 'label': 65, 'for': 65,
      'name': 60, 'placeholder': 60, 'title': 60, 'alt': 60,
      'exact-text': 52, 'text': 50,
      'xpath': 40,
      'css': 30,
      'value': 25,
      'xpath-absolute': 10,
    };
    function strategyTier(type) {
      if (type in STRATEGY_TIERS) return STRATEGY_TIERS[type];
      if (type.startsWith('data-')) return 80;   // other data-* attributes
      if (type.startsWith('aria-')) return 45;   // other aria-* attributes
      return 20;
    }
    // Sort exhaustive list into priority order; `unstable` entries demoted 35pts.
    function rankStrategies(rawList) {
      return (rawList || [])
        .map((s, i) => ({ s, i, score: strategyTier(s.type) - (s.unstable ? 35 : 0) }))
        .sort((a, b) => (b.score - a.score) || (a.i - b.i))
        .map(x => x.s);
    }
    function captureStrategies(el) {
      return rankStrategies(collectRawStrategies(el));
    }

    // ----- Floating Learn panel -----
    const panel = document.createElement('div');
    panel.id = '__learn_panel__';
    panel.style.cssText = `
      position: fixed; right: 12px; bottom: 12px; z-index: 2147483647;
      background: rgba(20,20,20,0.9); color: #fff; font: 12px sans-serif;
      padding: 8px 10px; border-radius: 8px; box-shadow: 0 2px 10px rgba(0,0,0,0.4);
      display:flex; gap:8px; align-items:center;
    `;
    panel.innerHTML = `
      <span style="font-weight:600;">Learn Mode</span>
      <button id="__learn_toggle_mark__" style="cursor:pointer;border:0;border-radius:6px;padding:4px 8px;">Marking: OFF</button>
      <span style="opacity:0.8;">(Shift+Click / DblClick / RightClick)</span>
    `;
    document.addEventListener('DOMContentLoaded', () => document.body.appendChild(panel));
    let markingMode = false;
    const toggleBtn = () => {
      const b = document.getElementById('__learn_toggle_mark__');
      if (!b) return;
      b.textContent = `Marking: ${markingMode ? 'ON' : 'OFF'}`;
      b.style.background = markingMode ? '#0a7' : '#444';
      b.style.color = '#fff';
    };
    document.addEventListener('click', (e) => {
      if (e.target && e.target.id === '__learn_toggle_mark__') {
        e.preventDefault(); e.stopPropagation();
        markingMode = !markingMode;
        toggleBtn();
      }
    }, true);

    // ----- Context menu for marking -----
    let menu;
    function closeMenu() {
      if (menu && menu.parentNode) menu.parentNode.removeChild(menu);
      menu = null;
    }

    function openMenu(x, y, el) {
      closeMenu();
      menu = document.createElement('div');
      menu.id = '__learn_ctx_menu__';
      menu.style.cssText = `
        position: fixed; left:${x}px; top:${y}px; z-index:2147483647;
        background:#1e1e1e; color:#fff; border:1px solid #333;
        border-radius:8px; padding:6px; font:12px sans-serif; min-width:160px;
      `;
      const items = [
        { label: 'Mark for verification', kind: 'verification' },
        { label: 'Mark mandatory', kind: 'mandatory' },
        { label: 'Mark popup', kind: 'popup' },
        { label: 'Mark error', kind: 'error' },
        { label: 'Mark business rule', kind: 'business_rule' },
        { label: 'Mark navigation', kind: 'navigation' },
      ];
      items.forEach(it => {
        const row = document.createElement('div');
        row.textContent = it.label;
        row.style.cssText = 'padding:6px 8px; cursor:pointer; border-radius:6px;';
        row.addEventListener('mouseenter', () => row.style.background = '#333');
        row.addEventListener('mouseleave', () => row.style.background = 'transparent');
        row.addEventListener('click', () => {
          const payload = {
            kind: it.kind === 'error' ? 'verification' : it.kind,
            selector: cssPath(el),
            label: getLabel(el),
            value: (el && 'value' in el ? el.value : (el.textContent || el.innerText || '')).toString().slice(0, 200),
            url: window.location.href,
            step: window.__learn_step__ || null
          };
          safeCall(() => window.recordHumanMark(payload));
          closeMenu();
        });
        menu.appendChild(row);
      });
      document.body.appendChild(menu);
    }

    document.addEventListener('click', () => closeMenu(), true);
    document.addEventListener('scroll', () => closeMenu(), true);

    document.addEventListener('contextmenu', (event) => {
      const target = event.target;
      if (!target || !(target instanceof HTMLElement)) return;
      event.preventDefault();
      openMenu(event.clientX, event.clientY, target);
    }, true);

    // ----- Existing CTA / submit / input capture -----
    window.addEventListener('click', event => {
      const target = event.target;
      if (!target || !(target instanceof HTMLElement)) return;
      const tag = target.tagName.toLowerCase();
      const type = (target.getAttribute('type') || '').toLowerCase();
      const role = target.getAttribute('role') || '';
      const ariaLabel = target.getAttribute('aria-label') || '';
      const dataTestId = target.getAttribute('data-testid') || target.getAttribute('data-test-id') || '';
      const text = (target.innerText || target.value || ariaLabel || '').trim();
      // Capture href for anchor tags (links) - walk up to find nearest anchor if clicked on child
      let href = '';
      if (tag === 'a') {
        href = target.getAttribute('href') || '';
      } else {
        const anchor = target.closest('a');
        if (anchor) href = anchor.getAttribute('href') || '';
      }
      
      // Check if click is on or inside a button element
      const parentButton = target.closest('button');
      const isClickOnButton = tag === 'button' || parentButton !== null;
      
      // Check if this is a navigation link (anchor with href that navigates)
      const parentAnchor = tag === 'a' ? target : target.closest('a');
      const anchorHref = parentAnchor ? parentAnchor.getAttribute('href') : '';
      const isNavigationLink = parentAnchor && anchorHref && anchorHref !== '#' && !anchorHref.startsWith('javascript:');
      
      // Check for MUI Accordion clicks (accordion header that expands/collapses content)
      // Also capture MUI Card headers that are clickable to expand/collapse
      const accordionSummary = target.closest('.MuiAccordionSummary-root') || 
                               target.closest('[role="button"][aria-expanded]') ||
                               target.closest('.MuiCardHeader-root');  // MUI Card headers are often clickable
      const isAccordionClick = accordionSummary !== null;

      // Check if click is inside a modal/popup/dialog container
      const modalAncestor = target.closest(
        '[role="dialog"], [role="alertdialog"], [aria-modal="true"], ' +
        '.modal.show, .modal[aria-hidden="false"], .modal-dialog, ' +
        '.popup-static, .custom_modal, ' +
        '.cdk-overlay-container, .mat-dialog-container, ' +
        '.MuiDialog-root, .MuiModal-root, ' +
        '.ant-modal-wrap, .p-dialog'
      );
      const isInsideModal = modalAncestor !== null;

      // Expanded button detection - includes anchors, divs styled as buttons, dropdown options, accordions
      const isButton =
        tag === 'button' ||
        parentButton !== null ||  // Clicked inside a button (SVG icon, etc.)
        (tag === 'input' && (type === 'submit' || type === 'button')) ||
        role === 'button' ||
        role === 'menuitem' ||
        role === 'option' ||
        role === 'tab' ||
        isNavigationLink ||  // Capture all navigation links
        isAccordionClick ||  // Capture MUI Accordion expand/collapse clicks
        (tag === 'a' && (target.classList.contains('btn') || target.classList.contains('button') || target.getAttribute('href') === '#' || !target.getAttribute('href'))) ||
        (tag === 'div' && (role === 'button' || target.classList.contains('btn') || target.classList.contains('button') || target.getAttribute('tabindex') === '0'));
      
      // Check for menu items FIRST (MUI MenuItem, etc.) - before dropdown option check
      // This prevents menu items from being incorrectly flagged as dropdown options
      const menuItemElement = target.closest('[role="menuitem"]') || target.closest('.MuiMenuItem-root');
      const isMenuItem = 
        role === 'menuitem' ||
        target.classList.contains('MuiMenuItem-root') ||
        menuItemElement !== null;

      // Also capture clicks on dropdown option elements (custom dropdowns like React-Select, MUI, etc.)
      // But NOT if it's already identified as a menu item
      // Also captures auto-suggest/typeahead suggestion list item clicks
      const isDropdownOption =
        !isMenuItem && (  // Don't flag as dropdown if it's a menu item
          role === 'option' ||
          role === 'listbox' ||
          target.classList.contains('option') ||
          target.classList.contains('dropdown-item') ||
          target.classList.contains('select-option') ||
          target.closest('[role="listbox"]') ||
          target.closest('.dropdown-menu') ||
          target.closest('.select-menu') ||
          // Auto-suggest / typeahead suggestion list patterns
          target.closest('[class*="autocomplete"]') ||
          target.closest('[class*="typeahead"]') ||
          target.closest('[class*="autosuggest"]') ||
          target.closest('[class*="suggestion"]') ||
          target.closest('[class*="combobox-list"]') ||
          target.closest('[aria-label*="suggestion"]') ||
          target.closest('ul[id*="typeahead"]') ||
          target.closest('ul[id*="autocomplete"]') ||
          // Angular-specific auto-suggest patterns
          target.closest('[class*="ng-option"]') ||
          target.closest('ng-dropdown-panel') ||
          // Common auto-complete list containers
          (target.closest('ul, ol') && target.closest('ul, ol').previousElementSibling &&
           target.closest('ul, ol').previousElementSibling.matches &&
           target.closest('ul, ol').previousElementSibling.matches('input[aria-autocomplete], input[role="combobox"], input[aria-owns], input[aria-controls]'))
        );
      // Note: Removed 'menu-item' class check and '[role="menu"]' check from dropdown detection
      // because these overlap with actual menu items (role="menuitem")

      // Human marking via Shift+Click or marking mode
      if (markingMode || event.shiftKey) {
        const payload = {
          kind: 'verification',
          selector: cssPath(target),
          label: getLabel(target) || text,
          value: (target.value || text || '').toString().slice(0, 200),
          url: window.location.href,
          step: window.__learn_step__ || null
        };
        safeCall(() => window.recordHumanMark(payload));
        return; // avoid double-recording as CTA click
      }

      // Record dropdown option selections (including auto-suggest items)
      if (isDropdownOption && text) {
        // Try to identify the associated input field (for auto-suggest)
        let associatedInput = '';
        const listContainer = target.closest('[role="listbox"], ul, ol, [class*="suggestion"], [class*="autocomplete"], [class*="typeahead"]');
        if (listContainer) {
          // Check if there's an input that owns/controls this list
          const listId = listContainer.id;
          if (listId) {
            const owningInput = document.querySelector(`input[aria-owns="${listId}"], input[aria-controls="${listId}"], input[list="${listId}"]`);
            if (owningInput) {
              associatedInput = owningInput.name || owningInput.id || owningInput.getAttribute('placeholder') || '';
            }
          }
          // Fallback: look for a nearby focused or recently-used input
          if (!associatedInput) {
            const nearbyInput = listContainer.previousElementSibling;
            if (nearbyInput && nearbyInput.matches('input')) {
              associatedInput = nearbyInput.name || nearbyInput.id || nearbyInput.getAttribute('placeholder') || '';
            }
          }
          // Fallback: find focused input on page
          if (!associatedInput) {
            const focusedInput = document.activeElement;
            if (focusedInput && focusedInput.matches('input')) {
              associatedInput = focusedInput.name || focusedInput.id || focusedInput.getAttribute('placeholder') || '';
            }
          }
        }
        window.recordClick({ tag, type, role, text: text.slice(0, 80), isDropdownOption: true, isAutoSuggestOption: !!associatedInput, associatedInput: associatedInput, selector: cssPath(target), href, strategies: captureStrategies(target) });
        return;
      }

      // Record menu item clicks (MUI MenuItem, etc.) - already checked earlier
      if (isMenuItem && text) {
        // Use the menu item element's selector for better targeting, not the inner element
        const menuEl = menuItemElement || target;
        const menuSelector = cssPath(menuEl);
        window.recordClick({ tag: menuItemElement ? menuItemElement.tagName.toLowerCase() : tag, type, role: 'menuitem', text: text.slice(0, 80), isMenuItem: true, selector: menuSelector, href, strategies: captureStrategies(menuEl) });
        return;
      }

      // Record MUI Accordion expand/collapse clicks
      if (isAccordionClick) {
        const ariaExpanded = accordionSummary.getAttribute('aria-expanded');
        const accordionText = (accordionSummary.innerText || accordionSummary.textContent || accordionSummary.getAttribute('aria-label') || '').trim().split('\n')[0].slice(0, 80);
        const accordionSelector = cssPath(accordionSummary);
        window.recordClick({
          tag: 'div',
          type,
          role: 'button',
          text: accordionText || 'accordion',
          selector: accordionSelector,
          href: '',
          isAccordion: true,
          ariaExpanded: ariaExpanded,
          strategies: captureStrategies(accordionSummary)
        });
        return;
      }

      // Record clicks on interactive elements inside modals/popups
      // (elements that don't match standard button patterns but are clearly clickable)
      const isModalInteractive = isInsideModal && !isButton && (
        window.getComputedStyle(target).cursor === 'pointer' ||
        window.getComputedStyle(target.parentElement || target).cursor === 'pointer' ||
        /\b(counter|card|item|tile|option|action|select|choice)\b/i.test(target.className) ||
        /\b(counter|card|item|tile|option|action|select|choice)\b/i.test((target.parentElement || target).className)
      );

      if (isModalInteractive) {
        let modalTarget = target;
        const container = target.closest('.counter, .counter-item, .card, .tile, [data-value], [data-id]')
          || target.closest('[style*="cursor: pointer"], [style*="cursor:pointer"]');
        if (container && modalAncestor.contains(container)) {
          modalTarget = container;
        }
        const modalText = (modalTarget.innerText || modalTarget.textContent || modalTarget.getAttribute('aria-label') || '').trim().split('\n')[0].slice(0, 80);
        if (modalText) {
          window.recordClick({
            tag: modalTarget.tagName.toLowerCase(),
            type,
            role: role || '',
            text: modalText,
            selector: cssPath(modalTarget),
            href: '',
            isModalAction: true,
            strategies: captureStrategies(modalTarget)
          });
          return;
        }
      }

      // Record navigation link clicks (anchor tags with real hrefs)
      if (isNavigationLink) {
        const linkText = (parentAnchor.innerText || parentAnchor.textContent || parentAnchor.getAttribute('aria-label') || '').trim().split('\n')[0].slice(0, 80);
        const linkSelector = cssPath(parentAnchor);
        // If the link has meaningful text, use it; otherwise use the href path for identification
        const effectiveLinkText = linkText || anchorHref.split('/').pop() || 'link';
        window.recordClick({
          tag: 'a',
          type,
          role,
          text: effectiveLinkText,
          selector: linkSelector,
          href: anchorHref,
          isNavigationLink: true,
          strategies: captureStrategies(parentAnchor)
        });
        return;
      }

      // For buttons without text (like avatar/icon buttons), try to get identifier from id, aria-label, or parent
      let buttonId = target.id || target.getAttribute('aria-label') || '';
      let buttonSelector = cssPath(target);
      
      // If we clicked inside a button (e.g., on SVG icon), use the button's attributes and selector
      if (parentButton) {
        buttonId = buttonId || parentButton.id || parentButton.getAttribute('aria-label') || parentButton.getAttribute('data-test-id') || parentButton.getAttribute('title') || '';
        // Use the button's CSS path, not the inner element's path
        buttonSelector = cssPath(parentButton);
      }
      
      // FALLBACK: Always record clicks on buttons with aria-haspopup (menu triggers) even if isButton is false
      // This catches edge cases where the button detection might fail
      if (parentButton && parentButton.hasAttribute('aria-haspopup')) {
        const menuBtnId = parentButton.id || parentButton.getAttribute('aria-label') || parentButton.getAttribute('data-test-id') || parentButton.getAttribute('title') || 'menu-button';
        const menuBtnSelector = cssPath(parentButton);
        window.recordClick({
          tag: 'button',
          type,
          role: 'button',
          text: menuBtnId,
          selector: menuBtnSelector,
          href: '',
          isIconButton: true,
          buttonId: menuBtnId,
          strategies: captureStrategies(parentButton)
        });
        return;
      }
      
      // LEAN RECORDER: icon-only buttons (trash/edit icons in grids) have no text, id or aria-label and
      // were dropped, leaving a gap in the journey. Name them from title / name / icon class instead.
      if (isButton && !text && !buttonId) {
        const btn = parentButton || target;
        const icon = btn.querySelector('i[class], svg[class], span[class*="icon"]');
        const iconClass = icon ? (String(icon.getAttribute('class') || '').split(/\s+/)
          .find(c => /icon|^bi-|^fa-|^k-i-|glyph|^mdi-/i.test(c) && !/^(oxd-icon|k-icon|icon|svg-inline--fa)$/i.test(c)) || '') : '';
        buttonId = btn.getAttribute('title') || btn.getAttribute('name') || iconClass || 'icon-button';
      }

      // Record button clicks - allow buttons with either text OR an id/aria-label
      if (!isButton || (!text && !buttonId)) return;
      
      // Get the actual button text - if we clicked inside a button, get text from the button element
      let buttonText = text;
      if (parentButton && !buttonText) {
        buttonText = (parentButton.innerText || parentButton.textContent || '').trim().split('\n')[0];
      }
      // If still no text, try aria-label
      if (!buttonText && parentButton) {
        buttonText = parentButton.getAttribute('aria-label') || '';
      }
      
      const effectiveText = buttonText || buttonId;
      window.recordClick({ tag: parentButton ? 'button' : tag, type, role, text: effectiveText.slice(0, 80), selector: buttonSelector, href, buttonId, strategies: captureStrategies(parentButton || target) });
    }, true);

    // Double-click marks value verification
    window.addEventListener('dblclick', event => {
      const target = event.target;
      if (!target || !(target instanceof HTMLElement)) return;
      const text = (target.innerText || target.value || '').trim();
      const payload = {
        kind: 'verification',
        selector: cssPath(target),
        label: getLabel(target) || text,
        value: (target.value || text || '').toString().slice(0, 200),
        url: window.location.href,
        step: window.__learn_step__ || null
      };
      safeCall(() => window.recordHumanMark(payload));
    }, true);

    // Track the last clicked element for form submit attribution
    let lastClickedElement = null;
    let lastClickedInfo = null;
    
    // Capture ALL clicks to track the button that triggers form submit
    document.addEventListener('click', event => {
      const target = event.target;
      if (!target || !(target instanceof HTMLElement)) return;
      
      // Check if this is a submit button or could trigger form submission
      const tag = target.tagName.toLowerCase();
      const type = (target.getAttribute('type') || '').toLowerCase();
      const role = target.getAttribute('role') || '';
      const text = (target.innerText || target.textContent || '').trim().split('\n')[0].slice(0, 80);
      
      // Store info about potential submit button clicks
      if (tag === 'button' || (tag === 'input' && (type === 'submit' || type === 'button'))) {
        lastClickedElement = target;
        lastClickedInfo = {
          tag,
          type,
          role,
          text,
          selector: cssPath(target),
          strategies: captureStrategies(target),
          timestamp: Date.now()
        };
      }
    }, true);
    
    document.addEventListener('submit', event => {
      const form = event.target;
      if (!(form instanceof HTMLFormElement)) return;
      const name = form.getAttribute('name') || form.id || '';
      
      // Try to identify the submit button that triggered this
      let submitButton = null;
      
      // Check if we have a recently clicked element (within 100ms)
      if (lastClickedInfo && (Date.now() - lastClickedInfo.timestamp) < 100) {
        submitButton = lastClickedInfo;
      } else {
        // Try to find the submit button in the form
        const submitBtn = form.querySelector('button[type="submit"], input[type="submit"], button:not([type])');
        if (submitBtn) {
          const btnText = (submitBtn.innerText || submitBtn.textContent || submitBtn.value || '').trim().split('\n')[0].slice(0, 80);
          submitButton = {
            tag: submitBtn.tagName.toLowerCase(),
            type: submitBtn.getAttribute('type') || '',
            role: submitBtn.getAttribute('role') || '',
            text: btnText,
            selector: cssPath(submitBtn),
            strategies: captureStrategies(submitBtn)
          };
        }
      }
      
      window.recordFormSubmit({ 
        formName: name,
        submitButton: submitButton
      });
    }, true);

    const lastSentValue = new WeakMap();  // LEAN RECORDER: last value recorded per field
    const onInputCapture = event => {
      const el = event.target;
      if (!el || !(el instanceof HTMLInputElement || el instanceof HTMLTextAreaElement)) return;
      
      const inputType = (el.getAttribute('type') || '').toLowerCase();
      const isCheckbox = inputType === 'checkbox' || el.getAttribute('role') === 'checkbox';
      const isRadio = inputType === 'radio' || el.getAttribute('role') === 'radio';
      
      // For radio buttons, record as a distinct radio event (not a generic input/fill)
      if (isRadio) {
        let name = el.name || el.id || '';
        let selectedLabel = '';
        // Try to find label text for MUI radio buttons
        const muiLabel = el.closest('.MuiFormControlLabel-root');
        if (muiLabel) {
          const labelText = muiLabel.querySelector('.MuiFormControlLabel-label, .MuiTypography-root');
          if (labelText) {
            selectedLabel = (labelText.textContent || '').trim();
          }
        }
        // Try aria-label or aria-labelledby
        if (!selectedLabel) {
          selectedLabel = el.getAttribute('aria-label') || '';
        }
        if (!selectedLabel) {
          const labelledBy = el.getAttribute('aria-labelledby');
          if (labelledBy) {
            const labelEl = document.getElementById(labelledBy);
            if (labelEl) selectedLabel = (labelEl.textContent || '').trim();
          }
        }
        // Fallback: look for closest label
        if (!selectedLabel) {
          const closestLabel = el.closest('label') || document.querySelector(`label[for="${el.id}"]`);
          if (closestLabel) {
            selectedLabel = (closestLabel.textContent || '').trim();
          }
        }
        // Fallback to value attribute
        if (!selectedLabel) {
          selectedLabel = el.value || '';
        }
        // Try to find the radio group label (fieldset legend or MUI FormLabel)
        let groupLabel = '';
        const fieldset = el.closest('fieldset');
        if (fieldset) {
          const legend = fieldset.querySelector('legend');
          if (legend) groupLabel = (legend.textContent || '').trim();
        }
        if (!groupLabel) {
          const radioGroup = el.closest('[role="radiogroup"]');
          if (radioGroup) {
            const grpLabel = radioGroup.getAttribute('aria-label') || '';
            if (grpLabel) groupLabel = grpLabel;
            if (!groupLabel) {
              const labelledBy = radioGroup.getAttribute('aria-labelledby');
              if (labelledBy) {
                const labelEl = document.getElementById(labelledBy);
                if (labelEl) groupLabel = (labelEl.textContent || '').trim();
              }
            }
          }
        }
        if (!groupLabel) {
          const muiFormControl = el.closest('.MuiFormControl-root');
          if (muiFormControl) {
            const formLabel = muiFormControl.querySelector('.MuiFormLabel-root');
            if (formLabel) groupLabel = (formLabel.textContent || '').trim();
          }
        }
        if (!name && !selectedLabel) return;
        const radioName = groupLabel || name || 'radio';
        window.recordInput({ name: radioName.replace(/\s+/g, '_').slice(0, 50), value: selectedLabel.slice(0, 80), isRadio: true, groupLabel: groupLabel, selectedLabel: selectedLabel, selector: cssPath(el), strategies: captureStrategies(el) });
        return;
      }
      
      // For checkboxes, try to find a meaningful name/label
      let name = el.name || el.id || '';
      if (isCheckbox && !name) {
        // Try to find label text for MUI checkboxes
        const muiLabel = el.closest('.MuiFormControlLabel-root');
        if (muiLabel) {
          const labelText = muiLabel.querySelector('.MuiFormControlLabel-label, .MuiTypography-root');
          if (labelText) {
            name = (labelText.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
        }
        // Try aria-label or aria-labelledby
        if (!name) {
          name = el.getAttribute('aria-label') || '';
        }
        if (!name) {
          const labelledBy = el.getAttribute('aria-labelledby');
          if (labelledBy) {
            const labelEl = document.getElementById(labelledBy);
            if (labelEl) name = (labelEl.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
        }
        // Fallback: look for closest label
        if (!name) {
          const closestLabel = el.closest('label') || document.querySelector(`label[for="${el.id}"]`);
          if (closestLabel) {
            name = (closestLabel.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
        }
        // Last resort for checkboxes
        if (!name) name = 'checkbox';
      }

      // For ALL inputs (text, textarea, etc.) without name/id, derive from label/placeholder/aria
      if (!isCheckbox && !name) {
        // Try placeholder
        name = (el.getAttribute('placeholder') || '').trim().replace(/\s+/g, '_').slice(0, 50);
        // Try aria-label
        if (!name) {
          name = (el.getAttribute('aria-label') || '').trim().replace(/\s+/g, '_').slice(0, 50);
        }
        // Try aria-labelledby
        if (!name) {
          const labelledBy = el.getAttribute('aria-labelledby');
          if (labelledBy) {
            const labelEl = document.getElementById(labelledBy);
            if (labelEl) name = (labelEl.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
        }
        // Try label[for] or closest label
        if (!name && el.id) {
          const lbl = document.querySelector(`label[for="${CSS.escape(el.id)}"]`);
          if (lbl) name = (lbl.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
        }
        if (!name) {
          const closestLabel = el.closest('label');
          if (closestLabel) {
            name = (closestLabel.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
        }
        // Try title attribute
        if (!name) {
          name = (el.getAttribute('title') || '').trim().replace(/\s+/g, '_').slice(0, 50);
        }
      }

      const value = isCheckbox ? (el.checked ? 'checked' : 'unchecked') : (el.value || '').toString();
      if (!name && !value) return;

      // Detect auto-suggest/typeahead inputs
      const isAutoSuggest = !!(
        el.getAttribute('aria-autocomplete') ||
        el.getAttribute('role') === 'combobox' ||
        el.getAttribute('aria-owns') ||
        el.getAttribute('aria-controls') ||
        el.getAttribute('list') ||
        el.classList.contains('autocomplete') ||
        el.classList.contains('typeahead') ||
        el.classList.contains('autosuggest') ||
        el.closest('[class*="autocomplete"]') ||
        el.closest('[class*="typeahead"]') ||
        el.closest('[class*="autosuggest"]')
      );

      // LEAN RECORDER: send the input type so password fields are masked whatever they are named
      lastSentValue.set(el, el.value);
      window.recordInput({ name, value: value.slice(0, 80), inputType: String(el.type || '').toLowerCase(), isCheckbox, isAutoSuggest, selector: cssPath(el), strategies: captureStrategies(el) });
    };
    document.addEventListener('input', onInputCapture, true);
    // LEAN RECORDER: masked/date inputs (Kendo DateInput, MaskedTextBox) show partial text while typing
    // ("12/2", "month/year") and reach their final value only when the user leaves the field. Record
    // that final value on focusout when it differs from the last one recorded. Autocomplete inputs are
    // skipped: their value comes from the option the user clicks, which is recorded as its own step.
    document.addEventListener('focusout', event => {
      const el = event.target;
      if (!el || !(el instanceof HTMLInputElement || el instanceof HTMLTextAreaElement)) return;
      if (!lastSentValue.has(el) || lastSentValue.get(el) === el.value) return;
      if (['checkbox', 'radio', 'file', 'hidden'].includes((el.type || '').toLowerCase())) return;
      if (el.getAttribute('role') === 'combobox' || el.hasAttribute('aria-autocomplete') || el.getAttribute('list')) return;
      onInputCapture({ target: el });
    }, true);

    // ----- Native select dropdown change capture -----
    document.addEventListener('change', event => {
      const el = event.target;
      if (!el) return;
      
      // Handle native <select> elements
      if (el instanceof HTMLSelectElement) {
        let name = el.name || el.id || '';
        // Derive name from label/aria when name/id are empty
        if (!name) {
          const lbl = getLabel(el);
          // getLabel may return concatenated option texts for <select> - avoid that
          // Instead try explicit label sources first
          const ariaLabel = (el.getAttribute('aria-label') || '').trim();
          if (ariaLabel) {
            name = ariaLabel.replace(/\s+/g, '_').slice(0, 50);
          } else if (el.id) {
            const labelEl = document.querySelector(`label[for="${CSS.escape(el.id)}"]`);
            if (labelEl) name = (labelEl.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
          if (!name) {
            const closestLabel = el.closest('label');
            if (closestLabel) name = (closestLabel.textContent || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
          // Try finding a sibling/parent label element (common pattern: label + select in same form-group)
          if (!name) {
            const formGroup = el.closest('.form-group, .field, .input-group, .form-field, [class*="form"]');
            if (formGroup) {
              const groupLabel = formGroup.querySelector('label, .label, .field-label, .control-label');
              if (groupLabel) {
                const labelText = (groupLabel.textContent || '').trim();
                if (labelText && labelText.length < 60) {
                  name = labelText.replace(/[*:]/g, '').trim().replace(/\s+/g, '_').slice(0, 50);
                }
              }
            }
          }
          if (!name) {
            name = (el.getAttribute('title') || '').trim().replace(/\s+/g, '_').slice(0, 50);
          }
        }
        const selectedOption = el.options[el.selectedIndex];
        const value = selectedOption ? selectedOption.value : '';
        const text = selectedOption ? selectedOption.text : '';
        const label = getLabel(el) || name;

        // Capture ALL available options in this <select> element
        const availableOptions = [];
        for (let i = 0; i < el.options.length; i++) {
          const opt = el.options[i];
          const optText = (opt.text || '').trim();
          const optValue = (opt.value || '').trim();
          // Skip placeholder/empty options (e.g., "-- Select --", "")
          if (!optValue && !optText) continue;
          if (/^-+\s*(select|choose|pick|option)/i.test(optText)) continue;
          availableOptions.push({
            value: optValue.slice(0, 80),
            text: optText.slice(0, 80),
            index: i
          });
        }

        window.recordSelectChange({
          name,
          value: value.slice(0, 80),
          text: text.slice(0, 80),
          label,
          selector: cssPath(el),
          strategies: captureStrategies(el),
          availableOptions: availableOptions.slice(0, 100)
        });
        return;
      }
      
      // Handle input elements with datalist or autocomplete (change fires after selection)
      if (el instanceof HTMLInputElement) {
        const name = el.name || el.id || '';
        const value = (el.value || '').toString();
        const listId = el.getAttribute('list');
        if (listId) {
          // This is a datalist-backed input
          window.recordSelectChange({
            name,
            value: value.slice(0, 80),
            text: value.slice(0, 80),
            label: getLabel(el) || name,
            selector: cssPath(el),
            isDatalist: true,
            strategies: captureStrategies(el)
          });
        }
      }
    }, true);

    // ----- Hover capture for dropdown menus (navbar, menus with submenus) -----
    let lastHoverTarget = null;
    let lastHoverSelector = null;  // Track by selector to prevent duplicates
    let hoverTimeout = null;
    const capturedHovers = new Set();  // Track all captured hovers to prevent duplicates
    
    document.addEventListener('mouseenter', event => {
      const target = event.target;
      if (!target || !(target instanceof HTMLElement)) return;
      
      const tag = target.tagName.toLowerCase();
      const role = target.getAttribute('role') || '';
      const ariaHasPopup = target.getAttribute('aria-haspopup');
      const ariaExpanded = target.getAttribute('aria-expanded');
      const text = (target.innerText || target.textContent || '').trim().split('\n')[0].slice(0, 80);
      const selector = cssPath(target);
      
      // STRICT detection: Only capture hovers that trigger menus/dropdowns
      // 1. Elements with aria-haspopup (standard accessible menus)
      const hasAriaPopup = ariaHasPopup === 'true' || ariaHasPopup === 'menu' || ariaHasPopup === 'listbox';
      
      // 2. Elements inside a menubar that could trigger submenus
      const isInMenubar = target.closest('[role="menubar"]') && (role === 'menuitem' || tag === 'a' || tag === 'button');
      
      // 3. Dropdown toggles (Bootstrap, etc.)
      const isDropdownToggle = target.classList.contains('dropdown-toggle') || 
                                target.getAttribute('data-toggle') === 'dropdown' ||
                                target.getAttribute('data-bs-toggle') === 'dropdown';
      
      // 4. MUI navigation items in AppBar/Toolbar that have expandable content
      const isMuiMenuTrigger = (
        target.closest('.MuiAppBar-root') || 
        target.closest('.MuiToolbar-root') ||
        target.closest('[role="navigation"]')
      ) && (
        target.closest('[aria-haspopup]') ||
        // Check if this element has a sibling/child menu that appears on hover
        target.parentElement?.querySelector('[role="menu"], [role="listbox"], .MuiMenu-root, .MuiPopover-root')
      );
      
      // 5. Nav items that visually expand (common pattern: nav item with nested menu)
      const isExpandableNavItem = (
        target.closest('nav') || target.closest('header')
      ) && (
        hasAriaPopup ||
        target.nextElementSibling?.matches('[role="menu"], .dropdown-menu, .submenu') ||
        target.parentElement?.querySelector(':scope > [role="menu"], :scope > .dropdown-menu, :scope > .submenu')
      );
      
      // Only capture if it's a genuine menu trigger
      const shouldCapture = hasAriaPopup || isInMenubar || isDropdownToggle || isMuiMenuTrigger || isExpandableNavItem;
      
      // Skip if not a menu trigger or no meaningful text
      if (!shouldCapture || !text || text.length < 2) return;
      
      // Create unique key for this hover (selector + text)
      const hoverKey = `${selector}::${text}`;
      
      // Skip if already captured this exact hover
      if (capturedHovers.has(hoverKey)) return;
      
      // Skip if same target (still hovering)
      if (lastHoverTarget === target || lastHoverSelector === selector) return;
      
      // Clear any pending hover timeout
      if (hoverTimeout) clearTimeout(hoverTimeout);
      
      // Delay capturing to filter out passing mouse movements (1.5s dwell time)
      hoverTimeout = setTimeout(() => {
        // Double-check we haven't captured this yet
        if (capturedHovers.has(hoverKey)) return;
        
        lastHoverTarget = target;
        lastHoverSelector = selector;
        capturedHovers.add(hoverKey);  // Mark as captured
        
        window.recordHover({
          tag,
          role,
          text,
          ariaHasPopup,
          ariaExpanded,
          selector,
          strategies: captureStrategies(target)
        });
      }, 1500); // 1.5s dwell time to filter accidental hovers
    }, true);
    
    // Reset hover tracking on mouse leave
    document.addEventListener('mouseleave', event => {
      const target = event.target;
      if (target === lastHoverTarget) {
        lastHoverTarget = null;
        lastHoverSelector = null;
      }
      if (hoverTimeout) {
        clearTimeout(hoverTimeout);
        hoverTimeout = null;
      }
    }, true);

    // ----- Popup/toast detection (existing, debounced) -----
    // Report a dialog/toast once when it appears: each report costs a full-page screenshot and a
    // DOM snapshot, and re-reporting it on every DOM change while it stays open bloated the raw log.
    let openNow = new Set();
    const handleMutations = debounce(() => {
      const seenNow = new Set();
      const dialogs = document.querySelectorAll(
        '[role="dialog"], [role="alertdialog"], .modal.show, .modal[aria-hidden="false"]'
      );
      dialogs.forEach(d => {
        const heading =
          d.getAttribute('aria-label') ||
          (d.querySelector('h1, h2, h3') && d.querySelector('h1, h2, h3').textContent) ||
          'dialog';
        const label = (heading || '').trim().slice(0, 80);
        seenNow.add('modal|' + label);
        if (!openNow.has('modal|' + label)) window.recordModalEvent({ type: 'open', label });
      });

      const alerts = document.querySelectorAll(
        '[role="alert"], .toast.show, .toast:not(.hide)'
      );
      alerts.forEach(a => {
        const text = (a.textContent || '').trim();
        if (!text) return;
        seenNow.add('toast|' + text.slice(0, 80));
        if (!openNow.has('toast|' + text.slice(0, 80))) window.recordToast({ label: text.slice(0, 80) });
      });
      openNow = seenNow;
    }, 500);

    const observer = new MutationObserver(handleMutations);
    // LEAN RECORDER: the script runs before <html> exists on a new page, so documentElement was null and
    // popup/toast detection never started; `document` always exists and sees the whole tree.
    observer.observe(document, {
      childList: true,
      subtree: true,
      attributes: true,
      attributeFilter: ['class', 'aria-hidden', 'role']
    });
  };

  // ========== INSTRUMENT PAGE FUNCTION ==========
  // This function sets up all the recording bindings and listeners for a page
  async function instrumentPage(targetPage, pageId) {
    // Guard: if the page already closed (e.g. instant popup), skip silently
    if (targetPage.isClosed()) {
      console.log(`[info] Page #${pageId} already closed before instrumentation, skipping.`);
      return null;
    }

    console.log(`[info] Instrumenting page #${pageId}: ${targetPage.url() || '(new page)'}`);
    
    // Track this page
    const pageInfo = { page: targetPage, id: pageId, url: targetPage.url() };
    allPages.push(pageInfo);
    
    // Set as active page
    activePage = targetPage;
    
    // ---------- Exposed bindings (from page -> node) ----------
    try {
      await targetPage.exposeBinding('recordClick', async (_source, data) => {
        // Ensure this page is active when event fires
        activePage = targetPage;
        await snap('click', `click_${(data && data.text) || ''}`, {
          type: 'click',
          tag: data && data.tag,
          inputType: data && data.type,
          role: data && data.role,
          text: data && data.text,
          href: data && data.href,
          selector: data && data.selector,
          isDropdownOption: data && data.isDropdownOption,
          isAutoSuggestOption: data && data.isAutoSuggestOption,
          associatedInput: data && data.associatedInput,
          isMenuItem: data && data.isMenuItem,
          isAccordion: data && data.isAccordion,
          isIconButton: data && data.isIconButton,
          buttonId: data && data.buttonId,
          strategies: (data && data.strategies) || [],
          pageId: pageId
        });
      });
    } catch (e) {
      // Binding may already exist if page was reloaded
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordClick on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordFormSubmit', async (_source, data) => {
        activePage = targetPage;
        const submitBtnInfo = data && data.submitButton;
        const metaData = {
          type: 'form_submit',
          formName: data && data.formName,
          pageId: pageId
        };
        
        // Include submit button info if available
        if (submitBtnInfo) {
          metaData.submitButton = {
            tag: submitBtnInfo.tag,
            type: submitBtnInfo.type,
            role: submitBtnInfo.role,
            text: submitBtnInfo.text,
            selector: submitBtnInfo.selector,
            strategies: submitBtnInfo.strategies || []
          };
        }
        
        await snap('form_submit', `form_${(data && data.formName) || ''}`, metaData);
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordFormSubmit on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordModalEvent', async (_source, data) => {
        activePage = targetPage;
        const modalType = (data && data.type) || 'modal';
        const label = (data && data.label) || modalType;
        await snap(`modal_${modalType}`, label, {
          type: 'modal',
          modalType,
          label,
          pageId: pageId
        });
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordModalEvent on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordToast', async (_source, data) => {
        activePage = targetPage;
        const label = (data && data.label) || 'toast';
        await snap('toast', label, {
          type: 'toast',
          label,
          pageId: pageId
        });
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordToast on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordInput', async (_source, data) => {
        activePage = targetPage;
        const isCheckbox = data && data.isCheckbox;
        const isRadio = data && data.isRadio;
        const isAutoSuggest = data && data.isAutoSuggest;
        const labelPrefix = isRadio ? 'radio' : (isCheckbox ? 'checkbox' : 'input');
        const eventType = isRadio ? 'radio' : (isCheckbox ? 'checkbox' : 'input');
        const snapPayload = {
          type: eventType,
          fieldName: data && data.name,
          value: data && data.value,
          isCheckbox: isCheckbox,
          isRadio: isRadio,
          isAutoSuggest: isAutoSuggest || false,
          inputType: (data && data.inputType) || undefined,
          selector: (data && data.selector) || '',
          strategies: (data && data.strategies) || [],
          pageId: pageId
        };
        // Include radio-specific metadata
        if (isRadio) {
          snapPayload.groupLabel = data.groupLabel || '';
          snapPayload.selectedLabel = data.selectedLabel || '';
          snapPayload.selector = data.selector || '';
        }
        await snap(labelPrefix, `${labelPrefix}_${(data && data.name) || ''}`, snapPayload);
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordInput on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordSelectChange', async (_source, data) => {
        activePage = targetPage;
        await snap('select_change', `select_${(data && data.name) || ''}`, {
          type: 'select_change',
          fieldName: data && data.name,
          value: data && data.value,
          selectedText: data && data.text,
          label: data && data.label,
          selector: data && data.selector,
          isDatalist: data && data.isDatalist,
          strategies: (data && data.strategies) || [],
          availableOptions: (data && data.availableOptions) || [],
          pageId: pageId
        });
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordSelectChange on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordHover', async (_source, data) => {
        activePage = targetPage;
        await snap('hover', `hover_${(data && data.text) || ''}`, {
          type: 'hover',
          tag: data && data.tag,
          role: data && data.role,
          text: data && data.text,
          ariaHasPopup: data && data.ariaHasPopup,
          ariaExpanded: data && data.ariaExpanded,
          selector: data && data.selector,
          strategies: (data && data.strategies) || [],
          pageId: pageId
        });
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordHover on page #${pageId}:`, e.message);
      }
    }

    try {
      await targetPage.exposeBinding('recordHumanMark', async (_source, mark) => {
        activePage = targetPage;
        try {
          const kind = (mark && mark.kind) || 'verification';
          const currentPage = getCurrentPage();
          const payload = {
            kind,
            selector: mark.selector || null,
            label: mark.label || null,
            value: mark.value || null,
            url: mark.url || (currentPage ? currentPage.url() : null),
            step: typeof mark.step === 'number' ? mark.step : step,
            timestamp: new Date().toISOString(),
            source: 'human',
            pageId: pageId
          };

          if (kind === 'popup') humanMarks.popup_marks.push(payload);
          else if (kind === 'mandatory') humanMarks.mandatory_marks.push(payload);
          else if (kind === 'business_rule') humanMarks.business_rule_marks.push(payload);
          else if (kind === 'navigation') humanMarks.navigation_marks.push(payload);
          else humanMarks.verification_marks.push(payload);

          await snap('human_mark', `human_${kind}`, { type: 'human_mark', mark: payload, pageId: pageId });
        } catch (e) {
          console.warn('[warn] recordHumanMark failed:', e.message || e);
        }
      });
    } catch (e) {
      if (!e.message.includes('has been already registered')) {
        console.warn(`[warn] Failed to expose recordHumanMark on page #${pageId}:`, e.message);
      }
    }

    // ---------- Inject client-side listeners ----------
    // Guard: page may have closed during expose-binding phase (fast popups)
    if (targetPage.isClosed()) {
      console.log(`[info] Page #${pageId} closed during binding setup, skipping script injection.`);
      return pageInfo;
    }

    try {
      await targetPage.addInitScript(clientSideScript);
    } catch(e) {
      console.log(`[debug] Could not addInitScript on page #${pageId}: ${e.message}`);
      return pageInfo;
    }

    try {
      await targetPage.evaluate(clientSideScript);
    } catch(e) {
      console.log(`[debug] Could not eval client side script in main frame: ${e.message}`);
    }

    // ---------- Also inject into all frames (for iframe support) ----------
    // Function to inject script into a frame
    async function injectScriptIntoFrame(frame) {
      try {
        await frame.evaluate(clientSideScript);
        console.log(`[info] Injected script into frame: ${frame.url()}`);
      } catch (e) {
        // Frame may not be ready or may be cross-origin
        console.log(`[debug] Could not inject into frame: ${e.message}`);
      }
    }
    
    // Inject into existing frames
    for (const frame of targetPage.frames()) {
      if (frame !== targetPage.mainFrame()) {
        await injectScriptIntoFrame(frame);
      }
    }
    
    // Listen for new frames and inject script
    targetPage.on('frameattached', async frame => {
      console.log(`[info] New frame attached: ${frame.url()}`);
      // Wait for frame to be ready
      try {
        await frame.waitForLoadState('domcontentloaded', { timeout: 5000 });
        await injectScriptIntoFrame(frame);
      } catch (e) {
        console.log(`[debug] Frame injection failed: ${e.message}`);
      }
    });

    // ---------- Page event listeners ----------
    targetPage.on('framenavigated', async frame => {
      if (frame === targetPage.mainFrame()) {
        activePage = targetPage;
        await snap('navigation', 'nav', { type: 'navigation', pageId: pageId });
      } else {
        // Re-inject script into navigated frame
        await injectScriptIntoFrame(frame);
      }
    });

    targetPage.on('domcontentloaded', async () => {
      activePage = targetPage;
      await snap('domcontentloaded', 'dom', { type: 'dom_loaded', pageId: pageId });
    });

    targetPage.on('load', async () => {
      activePage = targetPage;
      await snap('load', 'load', { type: 'load', pageId: pageId });
    });

    targetPage.on('dialog', async dialog => {
      activePage = targetPage;
      await snap('dialog', 'dialog', {
        type: 'dialog',
        message: dialog.message(),
        pageId: pageId
      });
      try { await dialog.dismiss(); } catch { /* ignore */ }
    });

    // Handle page close - switch back to previous page or finalize if last page
    targetPage.on('close', async () => {
      console.log(`[info] Page #${pageId} closed`);
      // Remove from tracked pages
      const idx = allPages.findIndex(p => p.page === targetPage);
      if (idx !== -1) {
        allPages.splice(idx, 1);
      }
      // Switch to the last remaining page
      if (allPages.length > 0) {
        const lastPage = allPages[allPages.length - 1];
        activePage = lastPage.page;
        page = activePage;  // Update legacy reference too
        console.log(`[info] Switched active page to #${lastPage.id}`);
      } else {
        // No more pages - finalize and close browser
        console.log(`[info] All pages closed, finalizing...`);
        activePage = null;
        page = null;
        await finalize('all_pages_closed');
        try {
          if (browser) await browser.close();
        } catch (e) {
          // Browser may already be closing
        }
        process.exit(0);
      }
    });

    return pageInfo;
  }

  // ========== BROWSER AND CONTEXT SETUP ==========
  browser = await firefox.launch({ 
    headless: false,
    args: ['--start-fullscreen', '--kiosk']
  });
  context = await browser.newContext({
    viewport: null,  // Use full screen size instead of default viewport
    ignoreHTTPSErrors: true
  });

  // Track the initial page ID so we can skip it in the 'page' event handler
  let initialPageId = null;

  // Create and instrument the initial page FIRST
  pageCounter++;
  initialPageId = pageCounter;
  page = await context.newPage();
  await instrumentPage(page, pageCounter);

  // Listen for new pages/popups AFTER creating the first page
  // This ensures we only capture truly NEW windows/popups
  context.on('page', async (newPage) => {
    // Skip if this is the initial page (already instrumented)
    if (allPages.some(p => p.page === newPage)) {
      return;
    }
    
    pageCounter++;
    const newPageId = pageCounter;
    console.log(`\n[info] ========== NEW WINDOW/POPUP DETECTED ==========`);
    console.log(`[info] New page opened (page #${newPageId})`);
    
    // ---- Phase 1: Capture popup metadata ASAP, before it can vanish ----
    let popupUrl = '';
    try { popupUrl = newPage.url(); } catch { /* already gone */ }

    // Register a close handler immediately so we record if it leaves fast
    let popupClosed = newPage.isClosed();
    let popupScreenshot = null;
    if (!popupClosed) {
      newPage.once('close', () => { popupClosed = true; });
    }

    // If already gone, record a minimal event and bail
    if (popupClosed) {
      console.log(`[info] Popup #${newPageId} already closed (url: ${popupUrl || 'unknown'}). Recording event.`);
      events.push({
        reason: 'popup_detected',
        label: `popup_closed_${newPageId}`,
        screenshot: null,
        step: step++,
        timestamp: new Date().toISOString(),
        url: popupUrl,
        type: 'popup_window',
        popupBehavior: 'instant_close',
        pageId: newPageId,
        parentPageId: newPageId - 1
      });
      console.log(`[info] =================================================\n`);
      return;
    }

    try {
      // ---- Phase 2: Wait for content (with a short timeout) ----
      try {
        await newPage.waitForLoadState('domcontentloaded', { timeout: 5000 }).catch(() => {});
      } catch { /* continue anyway */ }

      // Grab the URL again — it may have changed after navigation
      try { popupUrl = newPage.url(); } catch { /* closed during wait */ }

      // ---- Phase 3: Try to screenshot BEFORE heavy instrumentation ----
      // This captures the popup even if addInitScript/exposeBinding will fail
      // (e.g. browser-native PDF viewer, about:blank, chrome-extension pages)
      if (!popupClosed) {
        try {
          const safeLabel = `popup_${newPageId}`;
          const fileName = `step_${String(step).padStart(3, '0')}_${safeLabel}.png`;
          const filePath = path.join(screensDir, fileName);
          await newPage.screenshot({ path: filePath, fullPage: false, timeout: 3000 });
          popupScreenshot = `app_json_${scenario}_screens/${fileName}`;
          console.log(`[snap] popup screenshot -> ${filePath}`);
        } catch (e) {
          console.log(`[debug] Could not screenshot popup #${newPageId}: ${e.message}`);
        }
      }

      // Record the popup event in the timeline (even if we can't fully instrument)
      const popupEvent = {
        reason: 'popup_detected',
        label: `popup_${newPageId}`,
        screenshot: popupScreenshot,
        step: step++,
        timestamp: new Date().toISOString(),
        url: popupUrl,
        type: 'popup_window',
        pageId: newPageId,
        parentPageId: newPageId - 1
      };

      // Detect if this is a PDF or non-HTML resource
      const isPdfLikely = /\.pdf(\?|#|$)/i.test(popupUrl)
        || popupUrl.startsWith('blob:')
        || (popupUrl.includes('viewer') && popupUrl.includes('pdf'));
      if (isPdfLikely) {
        popupEvent.popupBehavior = 'pdf_viewer';
        console.log(`[info] Popup #${newPageId} appears to be a PDF viewer (${popupUrl})`);
      }

      events.push(popupEvent);

      // If the page closed during screenshot, we've still recorded the event
      if (popupClosed || newPage.isClosed()) {
        popupEvent.popupBehavior = popupEvent.popupBehavior || 'closed_after_capture';
        console.log(`[info] Popup #${newPageId} closed after screenshot capture.`);
        console.log(`[info] =================================================\n`);
        return;
      }

      // ---- Phase 4: Full instrumentation (for popups that stay open) ----
      const pageInfo = await instrumentPage(newPage, newPageId);
      
      // Take the full snap (with DOM metadata) now that instrumentation is done
      if (pageInfo && !newPage.isClosed()) {
        await snap('new_window', `new_window_${newPageId}`, { 
          type: 'new_window', 
          pageId: newPageId,
          parentPageId: newPageId - 1
        });
      }
      
      console.log(`[info] New window/popup is now being recorded!`);
    } catch (e) {
      // Popup closed or browser context destroyed — non-fatal
      console.warn(`[warn] Could not fully instrument popup #${newPageId}: ${e.message}`);
      // Ensure we still have an event even on error
      if (!events.some(ev => ev.pageId === newPageId && ev.type === 'popup_window')) {
        events.push({
          reason: 'popup_detected',
          label: `popup_error_${newPageId}`,
          screenshot: popupScreenshot,
          step: step++,
          timestamp: new Date().toISOString(),
          url: popupUrl,
          type: 'popup_window',
          popupBehavior: 'instrumentation_failed',
          error: e.message,
          pageId: newPageId,
          parentPageId: newPageId - 1
        });
      }
    }
    console.log(`[info] =================================================\n`);
  });

  console.log(`[info] Opening base URL: ${baseUrl}`);
  await page.goto(baseUrl);
  await snap('initial', 'initial', { type: 'initial' });

  console.log('\nInteract with the browser to exercise the scenario.');
  console.log('Screenshots will be captured on:');
  console.log('  - Navigations (frame navigated / page load)');
  console.log('  - Major CTA button clicks (heuristic)');
  console.log('  - Form submissions');
  console.log('  - Text inputs');
  console.log('  - Modal/dialog appearances');
  console.log('  - Toast/alert-like elements');
  console.log('  - Human marks (Shift+Click / DblClick / RightClick / Panel toggle)');
  console.log('  - NEW WINDOWS/POPUPS (automatically instrumented!)');
  console.log('\n📌 Multi-page support: New windows/popups are now automatically recorded!');
  console.log('   Right-click menu and all captures work in all windows.');
  console.log('\nClose the browser window or press Ctrl+C in this terminal when you are done.');

  browser.on('disconnected', async () => {
    console.log('\n[info] Browser disconnected, saving JSON log...');
    await finalize('browser_disconnected');
    process.exit(0);
  });

  const handleSigint = async () => {
    console.log('\n[info] Caught SIGINT, closing browser...');
    try {
      if (browser) {
        await browser.close();
      } else {
        await finalize('sigint_no_browser');
        process.exit(0);
      }
    } catch (e) {
      console.warn('[warn] Error while closing browser:', e.message || e);
      await finalize('sigint_error');
      process.exit(1);
    }
  };

  process.on('SIGINT', handleSigint);

  await new Promise(() => {});
})().catch((err) => {
  // The IIFE only settles via rejection (it otherwise waits forever for SIGINT),
  // so translate the most common failure — a missing/mismatched Playwright browser —
  // into a clear, actionable message instead of a raw unhandled-rejection dump.
  const msg = (err && (err.message || String(err))) || '';
  if (/Executable doesn't exist|please run the following command|ms-playwright|playwright install/i.test(msg)) {
    console.error('\n[error] Playwright Firefox is missing or its version does not match the "playwright" package.');
    console.error('[error] ' + msg.split('\n')[0]);
    console.error('[fix]   Run install.bat in this folder, or install the matching browser manually:');
    console.error('[fix]       npx --no-install playwright install firefox');
  } else {
    console.error('\n[error] Recorder failed:', msg);
  }
  process.exit(1);
});
'''


def find_qe_home(*starts: Path, explicit: Optional[str] = None) -> Path:
    """Folder whose node_modules has playwright + @cucumber/cucumber (the QE install)."""
    cands = [Path(explicit)] if explicit else []
    for s in starts:
        cands += [s, *s.parents]
    cands += [Path.cwd(), *Path.cwd().parents, Path(r"C:\QE\QEScriptsGenerator")]
    ok = lambda c: (c / "node_modules" / "playwright").is_dir() and (c / "node_modules" / "@cucumber" / "cucumber").is_dir()
    # prefer the full install (bundled browsers in ms-playwright) over a dev checkout with node_modules only
    for c in [c for c in cands if (c / "ms-playwright").is_dir()] + cands:
        if ok(c):
            return c.resolve()
    raise SystemExit("QE install not found (node_modules with playwright and @cucumber/cucumber): pass --qe-home")


def node_env(qe_home: Path) -> Dict[str, str]:
    env = dict(os.environ, NODE_PATH=str(qe_home / "node_modules"))
    if not env.get("PLAYWRIGHT_BROWSERS_PATH") and (qe_home / "ms-playwright").is_dir():
        env["PLAYWRIGHT_BROWSERS_PATH"] = str(qe_home / "ms-playwright")
    return env


def cmd_learn(project: Path, scenario: str, url: str, keep_passwords: bool, qe_home_arg: Optional[str],
              full_page: bool = False) -> Path:
    qe_home = find_qe_home(project, explicit=qe_home_arg)
    tool_dir = project / "recorded_journey" / "_recorder"
    tool_dir.mkdir(parents=True, exist_ok=True)
    recorder = tool_dir / "codegen_with_screenshots.js"  # lean copy; the IMAGE one is not touched
    recorder.write_text(RECORDER_JS.replace("/*__LEAN_RAW_LOG__*/", LEAN_JS), encoding="utf-8")
    cmd = ["node", str(recorder), "--project", str(project), "--scenario", scenario, "--url", url]
    if keep_passwords:
        cmd.append("--keep-passwords")
    if full_page:
        cmd.append("--full-page-screenshots")
    print(f"Learn: recording '{scenario}' - use the app in the browser that opens, close it when done.")
    subprocess.run(cmd, cwd=str(project.parent), env=node_env(qe_home), check=False)
    raw = project / "raw_logs" / f"app_json_{scenario}.json"
    if not raw.is_file():
        raise SystemExit(f"no raw log was written ({raw})")
    data = json.loads(raw.read_text(encoding="utf-8"))
    ev = data.get("events") or []
    acts = sum(1 for e in ev if e.get("type") in USER_ACTIONS)
    print(f"Learn: lean raw log {raw.stat().st_size / 1e6:.2f} MB, {len(ev)} events ({acts} user actions) -> {raw}")
    return raw


def cmd_generate(raw_path: Path, out: Optional[Path], name: Optional[str]) -> Path:
    if not raw_path.is_file():
        raise SystemExit(f"raw log not found: {raw_path}")
    name = name or re.sub(r"^app_json_", "", raw_path.stem)
    out = out or raw_path.parent.parent / "recorded_journey" / name
    try:
        raw = json.loads(raw_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        raise SystemExit(f"cannot read raw log: {e}")

    plan = build(raw)
    if not any(s["kind"] not in ("see", "message", "url", "goto") for s in plan["steps"]):
        raise SystemExit("no recorded user actions in this raw log: nothing generated")
    suspects = suspect_values(plan["data"])

    (out / "features").mkdir(parents=True, exist_ok=True)
    (out / "support").mkdir(exist_ok=True)
    (out / "testdata" / "files").mkdir(parents=True, exist_ok=True)
    (out / "features" / "recorded_journey.feature").write_text(render_feature(name, plan), encoding="utf-8")
    (out / "locators.json").write_text(json.dumps({"start_url": plan["start_url"], "controls": plan["controls"],
                                                   "expected_errors": plan["expected_errors"]},
                                                  indent=2, ensure_ascii=False), encoding="utf-8")
    (out / "support" / "recorded_journey.steps.ts").write_text(STEPS_TS, encoding="utf-8")
    (out / "cucumber.js").write_text(CUCUMBER_JS, encoding="utf-8")
    (out / "tsconfig.json").write_text(TSCONFIG, encoding="utf-8")
    action_kinds = [s for s in plan["steps"] if s["kind"] not in ("see", "message", "url", "goto")]
    report = {"raw_log": raw_path.name, "recorded_actions": plan["recorded_actions"], "steps": len(action_kinds),
              "checks": plan["checks_by_kind"], "not_turned_into_checks": plan["ignored"],
              "pages": dict(Counter(s["page"] for s in action_kinds)), "skipped": plan["skipped"], "suspect_values": suspects}
    (out / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")

    c = plan["checks_by_kind"]
    print(f"Generate '{name}': {len(action_kinds)} steps from {plan['recorded_actions']} recorded actions "
          f"({100.0 * len(action_kinds) / max(plan['recorded_actions'], 1):.1f}%), {len(plan['controls'])} controls, "
          f"{len(report['pages'])} pages")
    print(f"  checks: {c.get('see', 0)} marked elements, {c.get('message', 0)} popups/messages, {c.get('url', 0)} page changes")
    if plan["calendar_clicks"]:
        print(f"  WARNING: {plan['calendar_clicks']} click(s) inside a date-picker calendar: replaying calendar clicks is fragile."
              " Record again and TYPE the date into the field (then click into the next field).")
    if plan["generated_selects"]:
        print(f"  {len(plan['generated_selects'])} dropdown choice(s) look like ids that change per run "
              f"({', '.join(plan['generated_selects'])}): if the value is missing, the run picks the same position in the list")
    gotos = sum(1 for s in plan["steps"] if s["kind"] == "goto")
    if gotos:
        print(f"  {gotos} page change(s) had no recorded click: the test opens those pages directly (marked '# Note' in the feature)")
    if plan["ignored"]:
        print("  not turned into checks: " + ", ".join(f"{v} {k}" for k, v in plan["ignored"].items()))
    for s in plan["skipped"]:
        print(f"  skipped: step {s['raw_step']} {s['type']} on {s['page']} ({s['reason']})")
    if suspects:
        print(f"  {len(suspects)} test value(s) need a real value (edit the Examples row in the feature):")
        for s in suspects:
            print(f"   - {s['where']}: {s['reason']}")
    print(f"  -> {out}")
    return out


def cmd_run(out: Path, headless: bool, base_url: Optional[str], qe_home_arg: Optional[str]) -> int:
    if not (out / "cucumber.js").is_file():
        raise SystemExit(f"not a generated journey folder (no cucumber.js): {out}")
    qe_home = find_qe_home(out, explicit=qe_home_arg)
    env = node_env(qe_home)
    if headless:
        env["HEADLESS"] = "1"
    if base_url:
        env["BASE_URL"] = base_url
    cucumber = qe_home / "node_modules" / "@cucumber" / "cucumber" / "bin" / "cucumber.js"
    return subprocess.run(["node", str(cucumber), "--config", "cucumber.js"], cwd=str(out), env=env).returncode


def self_test() -> None:
    g = "29164a61-d33f-418a-b462-1bbdd840c485"
    ev = {"type": "click", "text": "Thank you", "strategies": [
        {"type": "id", "value": f"{g}_k-popup"}, {"type": "data-role", "value": "alert"},
        {"type": "exact-text", "value": "Thank you"}, {"type": "css", "value": "#\\32 9164a61-d33f-418a-b462-1bbdd840c485_k-popup"},
        {"type": "xpath-absolute", "value": "/html/body[1]/div[15]"}]}
    r = robust_strategies(ev)
    assert [s["type"] for s in r] == ["exact-text", "xpath-absolute"], r  # GUIDs + noise gone, text before position
    nxt = {"type": "click", "text": "Next", "strategies": [{"type": "exact-text", "value": "Next"},
           {"type": "xpath", "value": '//*[@id="wizard-1"]/button[1]'}, {"type": "css", "value": "button.k-button"}]}
    assert [s["type"] for s in robust_strategies(nxt)] == ["xpath"]  # shared text/class dropped when anchored
    sv = {s["where"] for s in suspect_values({"a": "03/0", "b": "7403-1_", "c": "a_b@example.com", "d": "****", "e": "03/2030"})}
    assert sv == {"a", "b", "d"}, sv
    pm = url_page_map(["https://x/Provider/Enroll/Step1", "https://x/app#/Patient/Basic", "https://x/"])
    assert pm["https://x/Provider/Enroll/Step1"] == "ProviderEnrollStep1Page" and pm["https://x/"] == "HomePage", pm
    assert _snake("_".join(_name_parts("ctl00$Main$Grid1$ctl00$ctl05$EditForm$BirthDatePicker$dateInput")[-2:])) == "birth_date_picker_date_input"
    assert _snake("_".join(_name_parts("AccountDetails.Username")[-2:])) == "account_details_username"
    assert _snake("_".join(_name_parts("first_name")[-2:])) == "first_name"
    assert url_pattern("https://x/Provider/12345/Details?a=1") == "/Provider/*/Details"
    assert url_pattern("https://x/Home/Index#/Patient/Basic?x=1") == "#/Patient/Basic"
    # a small recording: fill, click (navigates), toast twice + spinner, mark showing the typed value
    rec = {"events": [
        {"step": 1, "type": "navigation", "url": "https://x/login", "pageId": 1},
        {"step": 2, "type": "input", "url": "https://x/login", "pageId": 1, "fieldName": "user", "value": "bob",
         "strategies": [{"type": "id", "value": "user"}]},
        {"step": 3, "type": "click", "url": "https://x/login", "pageId": 1, "text": "Go", "strategies": [{"type": "id", "value": "go"}]},
        {"step": 4, "type": "navigation", "url": "https://x/home/42", "pageId": 1},
        {"step": 5, "type": "toast", "label": "Processing ...", "pageId": 1, "url": "https://x/home/42"},
        {"step": 6, "type": "toast", "label": "Welcome back", "pageId": 1, "url": "https://x/home/42"},
        {"step": 7, "type": "toast", "label": "Welcome back", "pageId": 1, "url": "https://x/home/42"},
        {"step": 8, "type": "human_mark", "url": "https://x/home/42", "mark": {"kind": "verification", "selector": "#who", "value": "bob", "label": "user"}},
        {"step": 9, "type": "click", "url": "https://x/home/42", "pageId": 1, "text": "Out", "strategies": [{"type": "id", "value": "out"}]},
    ]}
    plan = build(rec)
    kinds = [s["kind"] for s in plan["steps"]]
    assert kinds == ["fill", "click", "message", "url", "see", "click"] or kinds == ["fill", "click", "url", "message", "see", "click"], kinds
    see = next(s for s in plan["steps"] if s["kind"] == "see")
    assert see["text"] == "<user>", see  # mark text follows the test data
    assert plan["ignored"].get("repeated popup/toast reports") == 1 and plan["ignored"].get("loading/unnamed/volatile popups") == 1, plan["ignored"]
    feature = render_feature("t", plan)
    assert 'Then I should be on "/home/*"' in feature and 'And I should see message "Welcome back"' in feature, feature
    assert "/*__LEAN_RAW_LOG__*/" in RECORDER_JS and "function leanRawLog" in LEAN_JS
    print("self-test ok")


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(errors="replace")  # type: ignore[attr-defined]
    ap = argparse.ArgumentParser(description="Recorded-journey pipeline (Learn -> Generate -> Run), separate from the IMAGE pipeline.")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def project_args(p, url=False):
        p.add_argument("--project", required=True, help="project folder, e.g. C:\\QE\\QEScriptsGenerator\\ps01")
        p.add_argument("--scenario", required=True, help="scenario name, e.g. PS-01")
        if url:
            p.add_argument("--url", required=True, help="start URL of the app")
            p.add_argument("--keep-passwords", action="store_true", help="store typed passwords (default: masked as ****)")
            p.add_argument("--full-page-screenshots", action="store_true", help="capture the whole scrolling page (default: the visible screen)")
        p.add_argument("--qe-home", help="QE install folder with node_modules (default: found automatically)")

    project_args(sub.add_parser("learn", help="record a journey with the lean recorder"), url=True)
    g = sub.add_parser("generate", help="raw log -> feature + locators + step definitions")
    g.add_argument("--raw-log", help="raw log path (or --project + --scenario)")
    g.add_argument("--project")
    g.add_argument("--scenario")
    g.add_argument("--out", help="output folder (default: <project>/recorded_journey/<scenario>)")
    r = sub.add_parser("run", help="run a generated journey with Cucumber + Playwright")
    r.add_argument("--out", help="generated journey folder (or --project + --scenario)")
    r.add_argument("--project")
    r.add_argument("--scenario")
    r.add_argument("--headless", action="store_true")
    r.add_argument("--base-url", help="start URL to use instead of the recorded one")
    r.add_argument("--qe-home")
    project_args(sub.add_parser("all", help="learn, then generate"), url=True)
    sub.add_parser("self-test", help="check the generator logic")
    a = ap.parse_args()

    if a.cmd == "self-test":
        self_test()
        return 0
    if a.cmd in ("learn", "all"):
        raw = cmd_learn(Path(a.project).resolve(), a.scenario, a.url, a.keep_passwords, a.qe_home, a.full_page_screenshots)
        if a.cmd == "all":
            out = cmd_generate(raw, None, a.scenario)
            print(f"Next: python {Path(sys.argv[0]).name} run --out \"{out}\"")
        return 0
    if a.cmd == "generate":
        if a.raw_log:
            raw = Path(a.raw_log).resolve()
        elif a.project and a.scenario:
            raw = Path(a.project).resolve() / "raw_logs" / f"app_json_{a.scenario}.json"
        else:
            ap.error("generate needs --raw-log, or --project and --scenario")
        cmd_generate(raw, Path(a.out).resolve() if a.out else None, a.scenario)
        return 0
    if a.out:
        out = Path(a.out).resolve()
    elif a.project and a.scenario:
        out = Path(a.project).resolve() / "recorded_journey" / a.scenario
    else:
        ap.error("run needs --out, or --project and --scenario")
    return cmd_run(out, a.headless, a.base_url, a.qe_home)


if __name__ == "__main__":
    sys.exit(main())
