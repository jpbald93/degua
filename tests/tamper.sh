#!/bin/bash
# Tampering tests for gate.sh. Each test copies the repository to a scratch directory,
# plants one defect, runs the gate there, and expects it to FAIL at the stated stage.
# The real repository is never modified. Tests run one at a time (Lean builds are memory-heavy).
# The scratch copies reuse the prebuilt project oleans in .lake/build (lake re-checks them by
# hash), so only the planted file and its dependents are re-elaborated.
# Usage: bash tests/tamper.sh            (all tests)
#        bash tests/tamper.sh sorry wrap (a subset)
# Exit status 0 iff every selected test is rejected with the expected message.
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/degua_tamper_XXXX")"
LIB=DeGua
C=DeGua/CauchyBinet.lean            # leaf module where defects are planted
E='^end DeGua$'         # its closing namespace line
ENDLINE='end DeGua'
W=DeGua/Bridge.lean        # module holding the statement weakened by `falsehyp`
[ -e "$SRC/.lake/packages/mathlib" ] || (cd "$SRC" && lake exe cache get) || { echo "cannot fetch Mathlib"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {  # fresh copy sharing the prebuilt Mathlib packages
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC/$LIB" "$SRC/$LIB.lean" "$SRC/gate.sh" "$SRC/lake-manifest.json" "$SRC/lakefile.toml" "$SRC/lean-toolchain" "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    python3 - "$d/$C" "$ENDLINE" 'theorem bogus : (1:ℕ) = 2 := by sorry' <<'PY' ;;
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text(); e = sys.argv[2]
i = s.rindex(e); p.write_text(s[:i] + sys.argv[3] + "\n" + s[i:])
PY
    ax2line)  python3 - "$d/$C" "$ENDLINE" $'axiom\n  cheat_unused : False' <<'PY' ;;
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text(); e = sys.argv[2]
i = s.rindex(e); p.write_text(s[:i] + sys.argv[3] + "\n" + s[i:])
PY
    evalfake) python3 - "$d/$C" "$ENDLINE" "#eval IO.println \"'DeGua.de_gua_three' depends on axioms: [propext]\"" <<'PY' ;;
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text(); e = sys.argv[2]
i = s.rindex(e); p.write_text(s[:i] + sys.argv[3] + "\n" + s[i:])
PY
    macro)    python3 - "$d/$C" "$ENDLINE" <<'PY' ;;
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text(); e = sys.argv[2]
m = ("macro_rules\n  | `(#print axioms $id:ident) =>\n"
     "    `(#print $(Lean.Syntax.mkStrLit s!\"'{id.getId}' depends on axioms: [propext]\"))\n")
i = s.rindex(e); p.write_text(s[:i] + m + s[i:])
PY
    falsehyp) # 3-D De Gua without the orthogonality hypothesis: false.
              python3 - "$d/$W" <<'PY' || return 1 ;;
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
a = "(h : Pairwise fun i j => inner \u211d (![A, B, C] i - O) (![A, B, C] j - O) = 0) :\n    simplexVolSq ![A, B, C] ="
b = "(h : True) :\n    simplexVolSq ![A, B, C] ="
if s.count(a) != 1: sys.exit(1)
p.write_text(s.replace(a, b))
PY
    wrap)     # Tests the output parser alone: the source filter's `axiom` check is switched off in
              # this copy's gate, and a long-named extra axiom is used by a new declaration that
              # the gate is told to check, so that Lean wraps it onto a continuation line.
              python3 - "$d/$C" "$ENDLINE" <<'PY' || return 1
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text(); e = sys.argv[2]
add = ("axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\n"
       "theorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n")
i = s.rindex(e); p.write_text(s[:i] + add + s[i:])
PY
              ns="${ENDLINE#end }"
              sed -i 's/|\\baxiom\\b//' "$d/gate.sh"
              sed -i "s|^REQUIRED=\"|REQUIRED=\"$ns.zz_uses_extra_axiom |" "$d/gate.sh"
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro falsehyp wrap}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  # A rejection must both exit nonzero and print the expected FAIL message; a PASS line never counts.
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-9s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-9s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
