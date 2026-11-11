#!/usr/bin/env bash
# R18.2, the module-reference lint — the third mechanical detector, beside §7.2's two.
#
# Every name the emitter writes must be a name that resolves. The two detectors in §7.2
# guard against output that is *shaped* wrong; this one guards against output that is not
# output at all: a qualified reference to a module the translator never generated. That
# failure mode is the worst kind, because the translator reports `0 error(s)` and the
# breakage surfaces much later as an F* resolution error in a file nobody wrote — and if
# the module happens to be one F* can find for another reason, it may not surface at all.
#
# `Class_Object` and `Func_Object_ReferenceEquals` were both real: each was emitted by a
# walk that fell through to a name-mangling rule without first checking that the thing it
# was naming would be generated.
#
# Like the provenance lint, this reads the generated .fst/.fsti files rather than the
# compiler's account of them, so an emitter that forgets to record a reference fails just
# as loudly as one that invents it.
set -u

cd "$(dirname "$0")/.."
fail=0
checked=0

shopt -s nullglob
for out in test/*/out examples/*/out; do
    dir=$(dirname "$out")
    modules=("$out"/*.fst "$out"/*.fsti)
    [ ${#modules[@]} -eq 0 ] && continue

    report=$(python3 - "$dir" "$out" <<'PY'
import os, re, sys

dirname, out = sys.argv[1], sys.argv[2]

# What exists to be referred to: every module this directory generated, plus every Pulse
# module the user wrote by hand and handed to the translator (`[assembly: IncludePulse]`
# emits the module, but a checked-in .fst alongside the sources is equally legitimate).
emitted = set()
for root in (out, dirname):
    if not os.path.isdir(root):
        continue
    for f in os.listdir(root):
        stem, ext = os.path.splitext(f)
        if ext in (".fst", ".fsti"):
            emitted.add(stem)

# R36.3. A unit's modules may name the modules of the units it references, which their
# manifests list (transitively).
def referenced(d, seen):
    path = os.path.join(d, "unit.json")
    if d in seen or not os.path.isfile(path):
        return
    seen.add(d)
    import json
    with open(path) as f:
        manifest = json.load(f)
    if d != os.path.abspath(out):
        emitted.update(manifest["modules"])
    for r in manifest["references"]:
        referenced(r, seen)

referenced(os.path.abspath(out), set())

# Modules that come from outside the directory: the F* and Pulse standard libraries, and
# pal-csharp's own support library. A reference into these resolves through --include, and
# whether the module exists is F*'s business, not the lint's.
LIBRARY = ("Prims", "FStar", "Pulse", "PulseCore", "Steel")

def library(name):
    return name.split(".")[0] in LIBRARY

# A comment names modules freely — it is prose, and prose about a module the user wrote in
# C# is exactly what a generated file should contain. Only code is checked, so comments,
# string literals and F* attributes are blanked (not deleted: line numbers stay honest).
def strip(text):
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("(*", j): depth, j = depth + 1, j + 2
                elif text.startswith("*)", j): depth, j = depth - 1, j + 2
                else: j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j])); i = j
        elif text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(re.sub(r"[^\n]", " ", text[i:j])); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)

problems = []
for f in sorted(os.listdir(out)):
    if os.path.splitext(f)[1] not in (".fst", ".fsti"):
        continue
    text = open(os.path.join(out, f)).read()
    text = strip(text)

    # `module X = Y` introduces a local name for Y. X resolves by definition; Y is checked
    # like any other reference, so an alias cannot launder an unresolvable module.
    aliases = {}
    for m in re.finditer(r"^module\s+(\w+)\s*=\s*([\w.]+)\s*$", text, re.M):
        aliases[m.group(1)] = m.group(2)

    refs = set()
    for m in re.finditer(r"^open\s+([\w.]+)\s*$", text, re.M):
        refs.add(m.group(1))
    refs.update(aliases.values())

    # A qualified use: a dotted path whose segments are all capitalised, followed by a
    # final segment that is not. `m.Struct_Box.fld_Width` contributes `Struct_Box`,
    # because the leading `m.` fails the capitalisation test and is not consumed.
    for m in re.finditer(r"\b([A-Z]\w*(?:\.[A-Z]\w*)*)\.[a-z_]\w*", text):
        refs.add(m.group(1))

    for ref in sorted(refs):
        head = ref.split(".")[0]
        if head in aliases:
            continue          # resolved above, through the alias' right-hand side
        if library(ref) or ref in emitted:
            continue
        # A module may be referred to by a suffix of its name once it is opened; the lint
        # does not model that, so a bare capitalised head that matches nothing at all is
        # what it reports.
        problems.append((f, ref))

for f, ref in problems:
    print(f"{f}: `{ref}` names no generated module and no library module")
print(f"CHECKED {len(os.listdir(out))}")
PY
    )
    n=$(echo "$report" | sed -n 's/^CHECKED //p')
    checked=$((checked + ${n:-0}))
    bad=$(echo "$report" | grep -v '^CHECKED ' || true)
    if [ -n "$bad" ]; then
        echo "module-refs: $dir"
        echo "$bad" | sed 's/^/  /'
        fail=1
    fi
done

if [ $fail -ne 0 ]; then
    echo
    echo "A generated module refers to a module that was never generated (R18.2)."
    echo "The emitter formed a name without checking that the declaration it names is one"
    echo "it will emit. Fix the walk that formed the name, not the reference."
    exit 1
fi

echo "module-refs: OK ($checked file(s))"
