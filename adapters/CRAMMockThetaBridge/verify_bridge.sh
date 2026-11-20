#!/bin/sh
set -eu
cd "$(dirname "$0")"
exec python3 verify_bridge.py
