#!/usr/bin/env bash

set -ex
set -o pipefail

function fail() {
  echo $1 >&2
  exit 1
}

function assert_eval() {
  msg=$1
  shift
  if eval "$@"; then true; else fail $msg; fi
}

function assert_test() {
  msg=$1
  shift
  if test "$@"; then true; else fail $msg; fi
}

assert_test "Please set CHARON_HOME to the Charon directory" ! -z "$CHARON_HOME"
assert_test "Please set EURYDICE_HOME to the Eurydice directory" ! -z "$EURYDICE_HOME"
assert_test "Please set KRML_HOME to the KaRaMeL directory" ! -z "$KRML_HOME"

deps=()
libcrux_deps=()
no_hacl=0
no_charon=0
clean_cargo=0
clean_cfiles=0
extract=""
glue=$EURYDICE_HOME/include/eurydice_glue.h
features=""
eurydice_glue=1
karamel_include=1
unrolling=0
format=1
cpp17=

# Parse command line arguments.
all_args=("$@")
while [ $# -gt 0 ]; do
    case "$1" in
        --no-hacl) no_hacl=1 ;;
        --no-charon) no_charon=1 ;;
        -c | --clean)
          case "$2" in
            cargo) clean_cargo=1 ; shift ;;
            all)   clean_cargo=1 ;& # fallthrough!
            cfiles) clean_cfiles=1 ; shift ;;
            none) shift ;;
            -*) ;; # this is just the next argument, don't do anything
            *) fail "invalid argument to --clean: $2" ;;
          esac
          ;;
        -d | --dep) deps+=("libcrux_iot_$2") ; shift ;;
        --libcrux-dep) libcrux_deps+=("libcrux_$2") ; shift ;;
        --extract) extract="$2" ; shift ;;
        --config) config="$2"; shift ;;
        --out) out="$2"; shift ;;
        --glue) glue="$2"; shift ;;
        --no-glue) eurydice_glue=0 ;;
        --no-karamel_include) karamel_include=0 ;;
        --no-unrolling) unrolling=0 ;;
        --no-format) format=0 ;;
        --cpp17) cpp17=-fc++17-compat ;;
        *) fail "invalid parameter : $1" ;;
    esac

    shift
done

assert_test "Need to provide --extract parameter" ! -z "$extract"

repo_root=$(git rev-parse --show-toplevel)
workspace_root="$repo_root/libcrux-iot"
libcrux_workspace_root="$repo_root/libcrux"

extract_root="$repo_root/c/$extract"
extract_crate="libcrux-iot-$extract"
extract_crate_=$(sed s/-/_/g <<<$extract_crate)
extract_llbc_path=$workspace_root/${extract_crate_}.llbc
pkg_root=$workspace_root/$extract

# we will cd to a subdirectory later. We need to resolve paths, because relative paths won't bw valid anymore.
glue=$(realpath "$glue")
config=$(realpath "$config")

# We can't set the default value at the top, because `extract_root` depends on the arguments.
if [[ -z $config ]]; then
  config=$extract_root/extract.yaml
fi
if [[ -z $out ]]; then
  out=$extract_root/extracted
fi

if [[ "$clean_cargo" = 1 ]]; then
  (cd workspace_root; cargo clean -p $extract_crate)
fi

dep_args=("--include $extract_crate_ --start-from $extract_crate_")
for dep in "${deps[@]}"; do
    dep_arg="--include $dep --start-from $dep"
    dep_args+=("$dep_arg")
  # dep_crate="libcrux-iot-$dep"
  # dep_crate_=$(sed s/-/_/g <<<$dep_crate)
  # dep_llbc_path=$workspace_root/${dep_crate_}.llbc
  # dep_llbcs+=("$dep_llbc_path")
done

for dep in "${libcrux_deps[@]}"; do
    dep_arg="--include $dep --start-from $dep"
    dep_args+=("$dep_arg")
  # dep_crate="libcrux-iot-$dep"
  # dep_crate_=$(sed s/-/_/g <<<$dep_crate)
  # dep_llbc_path=$workspace_root/${dep_crate_}.llbc
  # dep_llbcs+=("$dep_llbc_path")
done
# for dep in "${libcrux_deps[@]}"; do
#   dep_crate="libcrux-$dep"
#   dep_crate_=$(sed s/-/_/g <<<$dep_crate)
#   dep_llbc_path=$workspace_root/${dep_crate_}.llbc
#   dep_llbcs+=("$dep_llbc_path")
# done

if [[ "$no_charon" = 0 ]]; then
  rm -rf "${dep_llbcs[@]}"

  # for dep in ${libcrux_deps[@]}; do
  #     dep_crate="libcrux-$dep"
  #     dep_src=$(cargo metadata --format-version=1 --manifest-path=$pkg_root/Cargo.toml | jq -r ".packages[] | select(.name==\"$dep_crate\") | .targets[].src_path")
  #     dep_src_root=$(dirname $(dirname $dep_src))
  #     dep_crate_=$(sed s/-/_/g <<<$dep_crate)
  #   # dep_pkg_root="$libcrux_workspace_root/$dep"
  #   dep_llbc_path=$workspace_root/${dep_crate_}.llbc

  #   # Because of a Charon bug we have to clean the dep crate.
  #   (cd $dep_src_root ; cargo clean -p $dep_crate)
  #   echo "Running charon (libcrux - $dep) ..."
  #   ( cd $dep_src_root &&
  #     RUSTFLAGS="--cfg eurydice" $CHARON_HOME/bin/charon cargo \
  #       --remove-associated-types '*' \
  #       --rustc-arg=-Cdebug-assertions=no \
  #       --dest-file=$dep_llbc_path)
  #   if ! [[ -f $dep_llbc_path ]]; then
  #       echo "😱😱😱 You are the victim of this bug: https://hacspec.zulipchat.com/#narrow/stream/433829-Circus/topic/charon.20declines.20to.20generate.20an.20llbc.20file"
  #       echo "Suggestion: rm -rf $workspace_root/target or cargo clean"
  #       echo "failed for libcrux dependency $dep: file $dep_llbc_path does not exist"
  #       file $dep_llbc_path
  #       exit 1
  #   fi
  # done

  # for dep in ${deps[@]}; do
  #   dep_crate="libcrux-iot-$dep"
  #   dep_crate_=$(sed s/-/_/g <<<$dep_crate)
  #   dep_pkg_root="$workspace_root/$dep"
  #   dep_llbc_path=$workspace_root/${dep_crate_}.llbc

  #   # Because of a Charon bug we have to clean the dep crate.
  #   (cd $workspace_root ; cargo clean -p $dep_crate)
  #   echo "Running charon ($dep) ..."
  #   ( cd $dep_pkg_root &&
  #     RUSTFLAGS="--cfg eurydice" $CHARON_HOME/bin/charon cargo \
  #       --remove-associated-types '*' \
  #       --rustc-arg=-Cdebug-assertions=no )
  #   if ! [[ -f $dep_llbc_path ]]; then
  #       echo "😱😱😱 You are the victim of this bug: https://hacspec.zulipchat.com/#narrow/stream/433829-Circus/topic/charon.20declines.20to.20generate.20an.20llbc.20file"
  #       echo "Suggestion: rm -rf $workspace_root/target or cargo clean"
  #       echo "failed for dependency $dep: file $dep_llbc_path does not exist"
  #       file $dep_llbc_path
  #       exit 1
  #   fi
  # done

  echo "Running charon ($extract) ..."
    ( cd $pkg_root &&
          RUSTFLAGS="--cfg eurydice" $CHARON_HOME/bin/charon cargo \
                   --preset eurydice \
                   ${dep_args[@]} \
                   --remove-associated-types '*' \
                   --rustc-arg=-Cdebug-assertions=no \
        $features )
else
    echo "Skipping charon"
fi

mkdir -p $out
cd $out

# Clean only when requesting it.
# Note that we can not extract for all platforms on any platform right now.
# Make sure to keep files from other platforms.
if [[ $clean_cfiles = 1 ]]; then
    rm -rf libcrux_*.c libcrux_*.h
    rm -rf internal/*.h
fi

# Write out infos about the used tools
[[ -z "$CHARON_REV" && -d $CHARON_HOME/.git ]] && export CHARON_REV=$(git -C $CHARON_HOME rev-parse HEAD)
[[ -z "$EURYDICE_REV" && -d $EURYDICE_HOME/.git ]] && export EURYDICE_REV=$(git -C $EURYDICE_HOME rev-parse HEAD)
[[ -z "$KRML_REV" && -d $KRML_HOME/.git ]] && export KRML_REV=$(git -C $KRML_HOME rev-parse HEAD)
[[ -z "$LIBCRUX_REV" ]] && export LIBCRUX_REV=$(git rev-parse HEAD)
if [[ -z "$FSTAR_REV" && -d $FSTAR_HOME/.git ]]; then
    export FSTAR_REV=$(git -C $FSTAR_HOME rev-parse HEAD)
else
    export FSTAR_REV=$(fstar.exe --version | grep commit | sed 's/commit=\(.*\)/\1/')
fi
rm -f code_gen.txt
echo "This code was generated with the following revisions:" >> code_gen.txt
echo -n "Charon: " >> code_gen.txt
echo "$CHARON_REV" >> code_gen.txt
echo -n "Eurydice: " >> code_gen.txt
echo "$EURYDICE_REV" >> code_gen.txt
echo -n "Karamel: " >> code_gen.txt
echo "$KRML_REV" >> code_gen.txt
echo -n "F*: " >> code_gen.txt
echo "$FSTAR_REV" >> code_gen.txt
echo -n "Libcrux: " >> code_gen.txt
echo "$LIBCRUX_REV" >> code_gen.txt

# Generate header
cat > header.txt <<EOF
/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
EOF
sed -e 's/^/ * /' code_gen.txt >> header.txt
echo " */" >> header.txt


# Run eurydice to extract the C code
echo "Running eurydice ..."
echo $EURYDICE_HOME/eurydice \
    --config "$config" -funroll-loops $unrolling \
    --header header.txt $cpp17 \
    "${dep_llbcs[@]}" $extract_llbc_path

$EURYDICE_HOME/eurydice \
    --config "$config" -funroll-loops $unrolling \
    --header header.txt $cpp17 \
    $extract_llbc_path

if [[ "$eurydice_glue" = 1 ]]; then
    cp "$glue" .
fi

if [[ "$karamel_include" = 1 ]]; then
    echo "Copying karamel/include ..."
    mkdir -p karamel
    cp -R "$KRML_HOME/include" karamel/
fi

if [[ "$format" = 1 ]]; then
    find . -type f -name '*.c' -and -not -path '*_deps*' -exec clang-format-18 --style=Google -i "{}" \;
    find . -type f -name '*.h' -and -not -path '*_deps*' -exec clang-format-18 --style=Google -i "{}" \;

    if [[ -d internal ]]; then
        clang-format-18 --style=Google -i internal/*.h
    fi
    if [[ -d intrinsics ]]; then
      clang-format-18 --style=Google -i intrinsics/*.h
    fi
fi
