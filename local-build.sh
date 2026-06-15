#!/usr/bin/env bash
set -euo pipefail

lake exe cache get
lake exe phrasebook
python3 -m http.server 8000 -d _out/html-multi/
