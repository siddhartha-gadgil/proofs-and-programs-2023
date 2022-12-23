#!/bin/bash
set -e
find PnP2023 -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > PnP2023.lean
printf '\ndef hello := "world"\n' >> PnP2023.lean
