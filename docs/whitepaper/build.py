#!/usr/bin/env python3
"""Build the bil white paper from whitepaper.src.html.

Everything that could drift is generated rather than typed:
  [[c:key1,key2]]          inline citation(s), linked to the source's URL in CITATIONS.md
  [[x:file|start|end]]     code excerpt from a .bil file: the first line containing `start`
                           through the next line containing `end` (or equal to it, if `end`
                           is written `=text`)
  [[trace:file]]           model-check / verify / run counterexample for a seeded bug
  [[run:file:name]]        value of `let name` printed by `bil run file`
  [[stats]]                per-model results table (verify + model-check, live)
  [[total:key]]            totals from the same runs (proved, states, systems, ltl, fns, models)
  [[refs]]                 the full reference list, generated from CITATIONS.md

Usage: python3 docs/whitepaper/build.py   (from the repo root, after `cargo build --release`)
"""

import html
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WP = ROOT / "docs" / "whitepaper"
BIL = ROOT / "target" / "release" / "bil"
DOMAINS = ROOT / "examples" / "domains"

URL_RE = re.compile(r"https?://[^\s)<>]+")


def bil(*args):
    out = subprocess.run([str(BIL), *args], capture_output=True, text=True, cwd=ROOT)
    return out.returncode, out.stdout + out.stderr


def strip_url(u):
    return u.rstrip(".,;")


def md_inline(s):
    """The small Markdown subset used in CITATIONS.md table cells."""
    s = html.escape(s, quote=False)
    s = re.sub(r"`([^`]+)`", r"<code>\1</code>", s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    s = re.sub(r"(?<![\w*])\*([^*]+)\*(?![\w*])", r"<em>\1</em>", s)

    def link(m):
        u = strip_url(m.group(0))
        tail = m.group(0)[len(u):]
        return f'<a href="{u}">{u}</a>{tail}'

    return URL_RE.sub(link, s)


def parse_citations():
    groups, refs, current = [], {}, None
    for line in (WP / "CITATIONS.md").read_text().splitlines():
        if line.startswith("## "):
            current = line[3:].strip()
            groups.append((current, []))
        m = re.match(r"\| `\[([a-z0-9_]+)\]` \| ([ABCD]) \| (.*) \| (.*) \| (.*) \|$", line)
        if m and current:
            key, tier, source, verified, supports = m.groups()
            urls = [strip_url(u) for u in URL_RE.findall(source)]
            refs[key] = dict(
                key=key, tier=tier, source=source, verified=verified,
                supports=supports, url=urls[0] if urls else None,
            )
            groups[-1][1].append(key)
    return groups, refs


GROUPS, REFS = parse_citations()
USED = set()


def cite(keys):
    parts = []
    for key in keys.split(","):
        key = key.strip()
        if key not in REFS:
            sys.exit(f"unknown citation key: {key}")
        USED.add(key)
        r = REFS[key]
        title = html.escape(re.sub(r"\s+", " ", URL_RE.sub("", r["source"]))[:160], quote=True)
        href = r["url"] or f"#ref-{key}"
        parts.append(f'<a class="cite" href="{href}" title="{title}">{key}</a>')
    return '<span class="cites">[' + ", ".join(parts) + "]</span>"


def excerpt(spec):
    file, start, end = spec.split("|")
    lines = (ROOT / file).read_text().splitlines()
    i = next((n for n, l in enumerate(lines) if start in l), None)
    if i is None:
        sys.exit(f"excerpt start not found: {spec}")
    # An end marker starting with "=" must match a whole (stripped) line exactly.
    if end.startswith("="):
        j = next((n for n in range(i, len(lines)) if lines[n].strip() == end[1:]), None)
    else:
        j = next((n for n in range(i, len(lines)) if end in lines[n]), None)
    if j is None:
        sys.exit(f"excerpt end not found: {spec}")
    body = "\n".join(lines[i : j + 1])
    return f'<pre class="code"><code>{html.escape(body)}</code></pre>'


def trace(file):
    path = DOMAINS / "seeded_bugs" / file
    out = []
    for cmd in ("verify", "model-check", "run"):
        code, text = bil(cmd, str(path))
        if code != 0:
            keep = [
                l for l in text.splitlines()
                if re.search(r"VIOLATION|LTL FAILED|RuntimeError|REFUTED|Counterexample:|BOUNDED \(|Init:|Step \d|Lasso|error:", l)
                and "VC:" not in l
            ]
            out.append(f"$ bil {cmd} {path.relative_to(ROOT)}   # exit {code}")
            out.extend(keep)
    if not out:
        sys.exit(f"seeded bug {file} was not caught")
    return f'<pre class="trace"><code>{html.escape(chr(10).join(out))}</code></pre>'


RUN_CACHE = {}


def run_value(spec):
    file, name = spec.rsplit(":", 1)
    if file not in RUN_CACHE:
        code, text = bil("run", str(ROOT / file))
        if code != 0:
            sys.exit(f"bil run {file} failed:\n{text}")
        RUN_CACHE[file] = text
    m = re.search(rf"^{re.escape(name)} = (.*)$", RUN_CACHE[file], re.M)
    if not m:
        sys.exit(f"no `{name}` in bil run {file}")
    return html.escape(m.group(1))


DOMAIN_NAMES = {
    "semiconductor_se_spe": "Semiconductor: SE-gated SPE anneal",
    "process_safety_reactor": "Process safety: reactor SIS",
    "robotics_cobot_cell": "Robotics: cobot SSM cell",
    "surgical_teleoperation": "Surgical robotics: teleoperation",
    "medical_infusion_pump": "Medical devices: PCA infusion pump",
    "manufacturing_press_cell": "Manufacturing: press guarding",
    "iiot_mqtt_qos2": "IIoT: MQTT QoS 2 and NE 43",
    "control_antiwindup_pi": "Control: anti-windup PI",
    "navigation_geofence": "Navigation: geofence and RTH",
    "automotive_acc": "Automotive: adaptive cruise",
    "aerospace_envelope": "Aerospace: envelope protection",
    "energy_bms_balancing": "Energy storage: BMS",
    "public_safety_traffic_rail": "Public safety: signals and crossing",
    "cybersecurity_zero_trust": "Cybersecurity: zero trust",
}

STATS, TOTALS = [], dict(models=0, fns=0, proved=0, bounded=0, systems=0, states=0, ltl=0)


def collect_stats():
    for stem in DOMAIN_NAMES:
        f = DOMAINS / f"{stem}.bil"
        vcode, vout = bil("verify", str(f))
        mcode, mout = bil("model-check", str(f))
        src = f.read_text()
        row = dict(
            stem=stem,
            fns=len(re.findall(r"^(?:fn|spec|proof) ", src, re.M)),
            proved=vout.count("PROVED (by"),
            bounded=vout.count("BOUNDED ("),
            systems=mout.count("=== Explicit-State"),
            states=sum(int(n) for n in re.findall(r"States explored: (\d+)", mout)),
            ltl=mout.count("LTL PROVED"),
            ok=vcode == 0 and mcode == 0,
        )
        if not row["ok"]:
            sys.exit(f"{stem} is not green:\n{vout}\n{mout}")
        STATS.append(row)
        TOTALS["models"] += 1
        for k in ("fns", "proved", "bounded", "systems", "states", "ltl"):
            TOTALS[k] += row[k]


def stats_table():
    rows = []
    for r in STATS:
        rows.append(
            f'<tr><td><a href="#{r["stem"]}">{html.escape(DOMAIN_NAMES[r["stem"]])}</a></td>'
            f'<td><code>{r["stem"]}.bil</code></td><td class="n">{r["fns"]}</td>'
            f'<td class="n">{r["proved"]}</td><td class="n">{r["bounded"]}</td>'
            f'<td class="n">{r["systems"]}</td><td class="n">{r["states"]}</td>'
            f'<td class="n">{r["ltl"]}</td></tr>'
        )
    t = TOTALS
    rows.append(
        f'<tr class="total"><td>Total</td><td>{t["models"]} models</td><td class="n">{t["fns"]}</td>'
        f'<td class="n">{t["proved"]}</td><td class="n">{t["bounded"]}</td><td class="n">{t["systems"]}</td>'
        f'<td class="n">{t["states"]}</td><td class="n">{t["ltl"]}</td></tr>'
    )
    head = (
        "<thead><tr><th>Use case</th><th>Model</th><th class=\"n\">Functions</th>"
        "<th class=\"n\">Obligations proved</th><th class=\"n\">Bounded only</th>"
        "<th class=\"n\">Systems</th><th class=\"n\">States explored</th>"
        "<th class=\"n\">LTL proved</th></tr></thead>"
    )
    return f'<div class="table-wrap"><table class="stats">{head}<tbody>{"".join(rows)}</tbody></table></div>'


TIER_NAMES = {
    "A": "Standard, specification or regulator",
    "B": "Peer-reviewed or scholarly",
    "C": "Manufacturer or patent",
    "D": "Secondary, corroboration only",
}


def references():
    out = []
    for group, keys in GROUPS:
        if not keys:
            continue
        items = []
        for k in keys:
            r = REFS[k]
            items.append(
                f'<li id="ref-{k}"><span class="ref-key">[{k}]</span>'
                f'<span class="tier tier-{r["tier"]}" title="{TIER_NAMES[r["tier"]]}">{r["tier"]}</span>'
                f'<div class="ref-body"><p>{md_inline(r["source"])}</p>'
                f'<p class="ref-meta"><span>Verified: {md_inline(r["verified"])}</span>'
                f'<span>Supports: {md_inline(r["supports"])}</span></p></div></li>'
            )
        out.append(f"<h3>{html.escape(group)}</h3><ol class=\"refs\">{''.join(items)}</ol>")
    return "\n".join(out)


def main():
    collect_stats()
    src = (WP / "whitepaper.src.html").read_text()
    subs = [
        (r"\[\[c:([^\]]+)\]\]", lambda m: cite(m.group(1))),
        (r"\[\[x:([^\]]+)\]\]", lambda m: excerpt(m.group(1))),
        (r"\[\[trace:([^\]]+)\]\]", lambda m: trace(m.group(1))),
        (r"\[\[run:([^\]]+)\]\]", lambda m: run_value(m.group(1))),
        (r"\[\[total:([a-z]+)\]\]", lambda m: str(TOTALS[m.group(1)])),
        (r"\[\[stats\]\]", lambda m: stats_table()),
    ]
    for pat, fn in subs:
        src = re.sub(pat, fn, src)
    src = src.replace("[[refs]]", references())
    unused = sorted(set(REFS) - USED)
    if unused:
        print("note: listed but not cited inline:", ", ".join(unused))
    (WP / "bil-white-paper.html").write_text(src)
    print(f"wrote docs/whitepaper/bil-white-paper.html ({len(src)//1024} KiB, {len(USED)} sources cited)")


if __name__ == "__main__":
    main()
