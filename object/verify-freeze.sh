#!/bin/bash
# Re-derive the frozen files from the source commit and compare byte-for-byte. rc 0 = intact, 1 = differs, 2 = source unreadable.
set -u
SEATREPO=${SEATREPO:?set SEATREPO to a clone of the private record repository that holds the source}
D=$(cd "$(dirname "$0")" && pwd)
SHA=f17b69171ab2ae856206e3d33e160d9775da3410
P=papers/o94/arxiv/o94-verification-agents.tex
git -C "$SEATREPO" cat-file -e "$SHA:$P" 2>/dev/null || { echo "FREEZE: cannot read source $SHA:$P"; exit 2; }
rc=0
check() { # file first last
  if git -C "$SEATREPO" show "$SHA:$P" | sed -n "$2,$3p" | cmp -s - "$D/$1"; then echo "FREEZE OK $1"; else echo "FREEZE DIFFERS $1"; rc=1; fi
}
check appendix-A.tex 474 585
check exhibits-section5.tex 333 371
exit $rc
