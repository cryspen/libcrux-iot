#! /usr/bin/env python3

import os
import argparse
import subprocess
import sys
from glob import glob

def shell(command, expect=0, cwd=None, env={}):
    subprocess_stdout = subprocess.DEVNULL

    print("Env:", env)
    print("Command: ", end="")
    for i, word in enumerate(command):
        if i == 4:
            print("'{}' ".format(word), end="")
        else:
            print("{} ".format(word), end="")

    print("\nDirectory: {}".format(cwd))

    os_env = os.environ
    os_env.update(env)

    ret = subprocess.run(command, cwd=cwd, env=os_env)
    if ret.returncode != expect:
        raise Exception("Error {}. Expected {}.".format(ret, expect))

def dependency_path(dep):
    """Attempt to retrieve the crate root path (as a UTF-8 string) of a dependency `dep`, identified by its crate name."""
    cargo_command = ["cargo",
               "metadata",
               "--format-version",
               "1"]
    jq_command = ["jq",
                  "-r",
                  f".packages | .[] | select(.name==\"{dep}\") | .manifest_path | split(\"/\") | .[:-1] | join(\"/\")"]
    cargo_res = subprocess.Popen(cargo_command, stdout=subprocess.PIPE)
    jq_output = subprocess.run(jq_command, stdin=cargo_res.stdout, capture_output=True, encoding="utf-8")
    if jq_output.returncode != 0:
        raise Exception("Error {}. Expected {}.".format(jq_output, 0))
    return jq_output.stdout.strip()
    
class extractAction(argparse.Action):

    def __call__(self, parser, args, values, option_string=None) -> None:
        # Extract libcrux-secrets
        # I did this once, and copied the resulting F* files to /proofs/fstar/secrets.
        # include_str = "+**"
        # interface_include = ""
        # cargo_hax_into = [
        #     "cargo",
        #     "hax",
        #     "into",
        #     "-i",
        #     include_str,
        #     "fstar",
        # ]
        # hax_env = {}
        # secrets_dir = dependency_path("libcrux-secrets")
        # print("Secrets at : {}".format(secrets_dir))
        # shell(
        #     cargo_hax_into,
        #     cwd=secrets_dir,
        #     env=hax_env,
        # )

        # Extract ml-kem
        includes = [
            "-**",
            "+libcrux_iot_ml_kem::vector::**",
            "+libcrux_iot_ml_kem::polynomial::**",
            "+libcrux_iot_ml_kem::serialize::**",
            "+libcrux_iot_ml_kem::ntt::**",
            "+libcrux_iot_ml_kem::invert_ntt::**",
            "+libcrux_iot_ml_kem::sampling::**",
            "+libcrux_iot_ml_kem::hash_functions::**",
            "-libcrux_iot_ml_kem::hash_functions::portable::**", # we can include this again once we have panic freedom in SHA3
            "+libcrux_iot_ml_kem::matrix::**",
            "+libcrux_iot_ml_kem::ind_cpa::**",
        ]
        include_str = " ".join(includes)
        # interface_include = "+** -libcrux_iot_ml_kem::types -libcrux_iot_ml_kem::constants"
        interface_include = "+** -libcrux_iot_ml_kem::vector::traits -libcrux_iot_ml_kem::types -libcrux_iot_ml_kem::constants"
        cargo_hax_into = [
            "cargo",
            "hax",
            "into",
            "-i",
            include_str,
            "fstar",
            "--z3rlimit",
            "80",
            "--interfaces",
            interface_include,
        ]
        hax_env = {}
        shell(
            cargo_hax_into,
            cwd=".",
            env=hax_env,
        )
        return None


class proveAction(argparse.Action):

    def __call__(self, parser, args, values, option_string=None) -> None:
        admit_env = {}
        if args.admit:
            admit_env = {"OTHERFLAGS": "--admit_smt_queries true"}
        shell(["make", "-j4", "-C", "proofs/fstar/extraction/"], env=admit_env)
        return None

class cleanAction(argparse.Action):

    def __call__(self, parser, args, values, option_string=None) -> None:
        shell(["rm"] + glob("./proofs/fstar/extraction/*.fst"))
        shell(["rm"] + glob("./proofs/fstar/extraction/*.fsti"))
        if args.all:
            shell(["rm"] + glob("./proofs/fstar/secrets/*.fst"))
            shell(["rm"] + glob("./proofs/fstar/secrets/*.fsti"))
        return None    

def parse_arguments():
    parser = argparse.ArgumentParser(
        description="Libcrux prove script. "
        + "Make sure to separate sub-command arguments with --."
    )
    subparsers = parser.add_subparsers()

    extract_parser = subparsers.add_parser(
        "extract", help="Extract the F* code for the proofs."
    )
    extract_parser.add_argument("extract", nargs="*", action=extractAction)

    prover_parser = subparsers.add_parser(
        "prove",
        help="""
        Run F*.

        This typechecks the extracted code.
        To lax-typecheck use --admit.
        """,
    )
    prover_parser.add_argument(
        "--admit",
        help="Admit all smt queries to lax typecheck.",
        action="store_true",
    )
    prover_parser.add_argument(
        "prove",
        nargs="*",
        action=proveAction,
    )

    clean_parser = subparsers.add_parser(
        "clean", help="Remove generated F* code for this crate, excluding extracted dependencies (unless `--all` is passed)`."
    )
    clean_parser.add_argument("clean", nargs="*", action=cleanAction)    
    clean_parser.add_argument("--all", help="Remove all extracted F*, including dependencies.", action="store_true")
    if len(sys.argv) == 1:
        parser.print_help(sys.stderr)
        sys.exit(1)

    return parser.parse_args()


def main():
    # Don't print unnecessary Python stack traces.
    sys.tracebacklimit = 0
    parse_arguments()


if __name__ == "__main__":
    main()
