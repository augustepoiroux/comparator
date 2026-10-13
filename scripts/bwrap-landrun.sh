#!/usr/bin/env bash
# Bubblewrap drop-in for landrun.
#
# Comparator invokes its sandbox as
#   landrun --best-effort --ro / --rw /dev -ldd -add-exec [--env NAME]* [--ro P]* [--rwx P]* [--rox P]* -- CMD ARGS
# (see `buildLandrunArgs` in Main.lean). This script accepts exactly that interface and runs CMD under
# `bwrap` with equivalent or stronger restrictions:
#   - the whole file system is read-only except the `--rw`/`--rwx` paths, which must not be symlinks
#     (a symlink would make the bind writable at its target instead);
#   - private /dev, /proc, /tmp and /run (no host sockets), and its own PID, IPC, UTS, cgroup and
#     network namespaces: no network, and every process spawned by CMD dies with it;
#   - all capabilities dropped and a new session (no terminal injection);
#   - like landrun, the environment is cleared and only the `--env` variables are passed.
#
# COMPARATOR_BWRAP_UNSHARE_NET=0 keeps CMD in the caller's network namespace, for container runtimes
# that refuse to create one. (Dependencies must be present either way: `lake build` cannot fetch them
# in an isolated namespace.)
#
# Unknown flags are an error rather than a guess: if Comparator starts passing a new landrun flag, this
# script must be updated to know whether it takes a value, otherwise the command line would be misparsed.
set -euo pipefail

BWRAP_ARGS=(
  --unshare-pid
  --unshare-ipc
  --unshare-uts
  --unshare-cgroup-try
  --cap-drop ALL
  --die-with-parent
  --new-session
  --clearenv
  --ro-bind / /
  --dev /dev
  --proc /proc
  --tmpfs /tmp
  --tmpfs /run
)
if [[ "${COMPARATOR_BWRAP_UNSHARE_NET:-1}" != 0 ]]; then
  BWRAP_ARGS+=(--unshare-net)
fi

while [[ $# -gt 0 ]]; do
  case "$1" in
    --)
      shift
      break
      ;;
    --ro|--rox)
      if [[ "$2" != "/" && -e "$2" ]]; then
        BWRAP_ARGS+=(--ro-bind "$2" "$2")
      fi
      shift 2
      ;;
    --rw|--rwx)
      if [[ -L "$2" ]]; then
        echo "bwrap-landrun.sh: refusing symlinked writable path: $2" >&2
        exit 1
      fi
      if [[ "$2" != "/dev" && -e "$2" ]]; then
        BWRAP_ARGS+=(--bind "$2" "$2")
      fi
      shift 2
      ;;
    --env)
      # landrun accepts both `NAME` (pass the current value) and `NAME=VALUE`.
      if [[ "$2" == *=* ]]; then
        BWRAP_ARGS+=(--setenv "${2%%=*}" "${2#*=}")
      elif [[ -n "${!2+x}" ]]; then
        BWRAP_ARGS+=(--setenv "$2" "${!2}")
      fi
      shift 2
      ;;
    --log-level|--bind-tcp|--connect-tcp)
      shift 2
      ;;
    --best-effort|-ldd|-add-exec|--unrestricted-filesystem|--unrestricted-network)
      shift 1
      ;;
    -*)
      echo "bwrap-landrun.sh: unknown landrun flag '$1'" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [[ $# -eq 0 ]]; then
  echo "bwrap-landrun.sh: no command given" >&2
  exit 2
fi

# Like landrun, resolve the command with our own PATH: the sandbox has none.
cmd=$1
shift
if [[ "$cmd" != */* ]]; then
  cmd=$(command -v -- "$cmd") || { echo "bwrap-landrun.sh: command not found: $cmd" >&2; exit 127; }
fi

exec bwrap "${BWRAP_ARGS[@]}" -- "$cmd" "$@"
