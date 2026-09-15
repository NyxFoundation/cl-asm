#!/usr/bin/env sh
set -eu

lake exe codegen -- --program weigh_justification_and_finalization --asm-only -o gen-out/weigh_justification_and_finalization
