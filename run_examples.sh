#!/usr/bin/env bash
set -euo pipefail

examples_dir="$(dirname "$0")/examples"

for simf in "$examples_dir"/*.simf; do
    base=$(basename "$simf" .simf)
    args_file="$examples_dir/$base.args"

    base_args=("$simf" "--deny-warnings")
    if [ -f "$args_file" ]; then
        base_args+=("-a" "$args_file")
    fi

    # Run without witness
    echo ""
    echo "=== $base (no witness) ==="
    cargo run -- "${base_args[@]}"

    # Run once per .wit file
    for wit in "$examples_dir/$base".*.wit "$examples_dir/$base".wit; do
        [ -f "$wit" ] || continue
        echo ""
        echo "=== $base + $(basename "$wit") ==="
        cargo run -- "${base_args[@]}" -w "$wit"
    done
done
