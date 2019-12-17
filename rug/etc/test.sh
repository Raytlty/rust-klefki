#!/bin/bash

# Copyright © 2016–2019 University of Malta

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved. This file is offered as-is,
# without any warranty.

printf '%s*- mode: compilation; default-directory: "%s" -*-\n' - "$PWD"
printf 'Compilation started at %s\n\n' "$(date)"

function check_error {
    code="$?"
    if [ "$code" == "0" ]; then
        return
    fi
    printf '\nCompilation exited abnormally with code %s at %s\n' \
        "$code" "$(date)"
    exit "$code"
}

for word in "$@"; do
    arr=(X${word}X)
    count=${#arr[*]}
    if [ $count != 1 ]; then
        printf 'Expected single parameter, got "%s"\n' "$word"
        (exit 2)
        check_error
    fi
done

if [ -e target ]; then
    rm -r target
fi

suffix=""
if [[ "$1" == "-"* ]]; then
    suffix="$1"
    shift
fi

if [ $# == 0 ]; then
    toolchains=(beta stable nightly 1.31.1)
else
    toolchains=("$@")
fi

function print_eval_check {
    printf '$'
    for word in "$@"; do
        if [[ "$word" != *\ * ]]; then
            printf ' %q' "$word"
        elif [[ "$word" =~ ^[\ /0-9A-Z_a-z-]*$ ]]; then
            printf ' "%s"' "$word"
        else
            printf ' %q' "$word"
        fi
    done
    printf '\n'
    eval $(printf '%q ' "$@") 2>&1
    check_error
}

function tc {
    if [ "$1" != "" ]; then
        echo +$1$suffix
    fi
}

# Cache all C libraries.
print_eval_check \
    cargo $(tc "${toolchains[0]}") check \
    --no-default-features --features "gmp-mpfr-sys/mpc gmp-mpfr-sys/ctest" \
    -p gmp-mpfr-sys -p rug

# For all toolchains, check with default features and serde.
for toolchain in "${toolchains[@]}"; do
    if [[ "$toolchain" == beta* ]]; then
        check="clippy --all-targets"
    else
        check="check --all-targets"
    fi
    print_eval_check \
        cargo $(tc "$toolchain") $check \
        --features "fail-on-warnings serde" \
        -p gmp-mpfr-sys -p rug
done

# For first toolchain, check with all feature combinations.
# integer,rational = rational
# integer,rand = rand
# float,complex = complex
for features in \
    '' gmp-mpfr-sys{,/mpfr,/mpc} \
    integer{,\ float,\ complex}{,\ serde} \
    rational{,\ float,\ complex}{,\ rand}{,\ serde} \
    float{,\ rand}{,\ serde} \
    complex{,\ rand}{,\ serde} \
    rand{,\ serde} \
    serde
do
    toolchain="${toolchains[0]}"
    if [[ "$toolchain" == beta* ]]; then
        check=clippy
    else
        check=check
    fi
    if [[ "$features" =~ ^(()|serde)$ ]]; then
        gmp=""
    else
        gmp="-p gmp-mpfr-sys"
    fi
    features="fail-on-warnings${features:+ $features}"
    print_eval_check \
        cargo $(tc "$toolchain") $check --all-targets \
        --no-default-features --features "$features" \
        $gmp -p rug
done

rm -r target

# For all toolchains (including first), test with default features and serde
for toolchain in "${toolchains[@]}"; do
    for build in "" --release; do
        print_eval_check \
            cargo $(tc "$toolchain") test $build \
            --features "fail-on-warnings serde" \
            -p gmp-mpfr-sys -p rug
        rm -r target
    done
done

printf '\nCompilation finished at %s\n' "$(date)"
