# Install Lean, and a Rocq trial, on this machine

Written on 21 November 2026 for this machine: Windows 11, 16 cores, 32 GB of memory, 24 GB free on
C:, 81 GB free on D:, with Git, Docker Desktop and WSL 2 present.

The instructions use Simplified Technical English: one instruction in each sentence.

## What was read to write this guide

| Subject | Source, read on 21 November 2026 |
|---|---|
| Lean version manager `elan` | README of https://github.com/leanprover/elan ; newest release v4.4.0 of 18 November 2026 |
| Lean manual install | https://lean-lang.org/install/manual/ |
| Mathlib build cache | https://leanprover-community.github.io/install/project.html |
| Rocq Docker images | README of https://github.com/rocq-community/docker-rocq ; tag lists on Docker Hub |
| Rocq dependency plugin | package list `coq-dpdgraph` in https://github.com/rocq-prover/opam |

Section 5 says which steps come from these sources and which steps are a precaution of the writer.

## What the install adds to the machine

| Item | Place | Size |
|---|---|---|
| `elan` and each Lean version | `D:\elan` | To be measured; one Lean version is several hundred MB |
| Lean sources and their builds | `D:\lw` | To be measured; one Mathlib build cache is several GB |
| One user environment variable | `ELAN_HOME = D:\elan` | |
| One entry in the user PATH | `D:\elan\bin` | The installer adds it |
| One Docker image for Rocq | Docker's disk, which is on D: | 1.1 GB compressed |
| Rocq work folder | `D:\rw` | Small |

Nothing goes on C: except the environment variable and the PATH entry.

## 1. Install Lean

Use **Command Prompt**, not PowerShell. This machine has Windows PowerShell 5.1. The official
instructions require Command Prompt or PowerShell 7.4.1 or newer.

**Step 1. Set the install folder.**

1. Open Command Prompt: press the Windows key, type `cmd`, press Enter.
2. Type this command:
   ```
   setx ELAN_HOME D:\elan
   ```
3. Close the Command Prompt window.
4. Open a new Command Prompt window.
5. Type `echo %ELAN_HOME%`.

Result: the window shows `D:\elan`.

**Step 2. Install `elan`.**

1. Type these three commands, one at a time:
   ```
   curl -O --location https://elan.lean-lang.org/elan-init.ps1
   powershell -ExecutionPolicy Bypass -f elan-init.ps1
   del elan-init.ps1
   ```
   **In PowerShell, write `curl.exe` in place of `curl`.** In Windows PowerShell 5.1 the name `curl`
   is a short name for a different command. That command saves the download in a file with the
   name `--location`, and the second line then finds no `elan-init.ps1`. If this occurred, delete
   the file with `Remove-Item -LiteralPath '.\--location'` and type the first line again with
   `curl.exe`. In PowerShell, also make sure that `echo $env:ELAN_HOME` shows `D:\elan`.
2. Read the install location that the installer shows.
3. If the location is `D:\elan`, type `1` and press Enter.
4. If the location is not `D:\elan`, cancel the installer and stop. Do not continue.

**Step 3. Make sure that the install is correct.**

1. Close the Command Prompt window.
2. Open a new Command Prompt window.
3. Type `elan --version`.
4. Type `where lake`.

Result: the first command shows `elan 4.4.0` or newer. The second command shows a path that starts
with `D:\elan\bin`.

**Step 4. Permit long file paths in Git.** This is a precaution. Windows has a limit of 260
characters for a path, and this machine has the limit on.

```
git config --global core.longpaths true
```

## 2. Get the first Lean source: Mathlib at the commit of the library

The library has 12 entries from Mathlib at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`. This
commit uses Lean `v4.36.0-rc2`.

1. Type these commands, one at a time:
   ```
   mkdir D:\lw
   cd /d D:\lw
   git clone --filter=blob:none https://github.com/leanprover-community/mathlib4.git
   cd mathlib4
   git checkout e1545ebed97594477bbd88b2fe948ffce56e5af2
   type lean-toolchain
   ```
   Result: the last command shows `leanprover/lean4:v4.36.0-rc2`.

   In PowerShell, write `cd D:\lw` in place of `cd /d D:\lw`. The form with `/d` is for Command
   Prompt only. In PowerShell, also write `where.exe lake` in place of `where lake`: the plain
   name `where` is a different command there and shows nothing.
2. Get the files that the Mathlib project built in advance:
   ```
   lake exe cache get
   ```
   This command first downloads Lean `v4.36.0-rc2`. Then it downloads the build files. It does not
   compile Mathlib.
3. Make sure that Lean accepts one file:
   ```
   lake build Mathlib.Order.Basic
   ```
   Result: the command completes in a short time and shows no error.

**If `lake exe cache get` shows an error about `schannel` or about files that are not there:** an
antivirus program can stop the downloads. The official page says to stop the antivirus program for
the download and then to type `lake exe cache get!`.

**If a command shows an error about a path that is too long:** tell me the error. The repair is
one registry setting, and it needs administrator rights.

After this step, tell me. I then measure the disk use and the time, and I write the script that
reads the dependencies from the compiler.

## 3. Rocq trial in Docker

The plugin `coq-dpdgraph` gives the dependencies that the Rocq compiler records. Its newest
release is for Rocq 9.1. Thus the trial uses the image `rocq/rocq-prover:9.1`.

1. Start Docker Desktop.
2. Open Command Prompt.
3. Type these commands, one at a time:
   ```
   mkdir D:\rw
   docker pull rocq/rocq-prover:9.1
   docker run -it --name rocq91 -v D:\rw:/work -w /work rocq/rocq-prover:9.1 bash
   ```
   The last command opens a shell inside the container.
4. In that shell, type these commands, one at a time:
   ```
   rocq --version
   opam update
   opam install -y coq-dpdgraph
   opam list | grep -i dpdgraph
   exit
   ```

Result: the first command shows version 9.1. The fourth command shows `coq-dpdgraph` with version
`1.0+9.1`.

If `opam` does not find the package, stop and tell me the message. The image then needs one more
package repository, and I give you the command.

To open the same container again, type `docker start -ai rocq91`. The container keeps the plugin.
The folder `D:\rw` on Windows is the folder `/work` in the container.

A source that needs Coq 8.20 or older uses a different image: `coqorg/coq:8.20`, for example. I
select the image for each source when we get there.

After this step, tell me. I then write the script that extracts the dependencies, and I test it on
the Rocq standard library first.

## 4. Remove everything

**Lean.**

```
elan self uninstall
rmdir /s /q D:\lw
reg delete HKCU\Environment /v ELAN_HOME /f
```

**Rocq.**

```
docker rm rocq91
docker rmi rocq/rocq-prover:9.1
rmdir /s /q D:\rw
```

## 5. What comes from the official sources, and what does not

| Step | Origin |
|---|---|
| The three commands that install `elan`; the choice `1` | Official: `elan` README and the Lean manual install page |
| The default place `%USERPROFILE%\.elan` and the variable `ELAN_HOME` | Official: `elan` README names the two. The README does not say in words that the installer reads `ELAN_HOME`. Step 2 makes you check the location for this reason |
| `lake exe cache get`, and `lake exe cache get!` after an antivirus error | Official: Lean community project page |
| `elan self uninstall` | Official: `elan` README |
| Images `rocq/rocq-prover` for Rocq 9.0 and newer, `coqorg/coq` for 8.20.1 and older | Official: `docker-rocq` README |
| The tag `9.1` and the plugin version `1.0+9.1` | Read from Docker Hub and from the opam package list |
| All folders on D:, the short folder names, `git clone --filter=blob:none`, `core.longpaths` | Precaution of the writer, because of the free space on C: and the path limit |

## 6. What this guide does not cover

- The VS Code extension for Lean. The batch work of this repository does not need it. The official
  install page describes it.
- The other 39 Lean sources. Each has its own Lean version and, in most cases, its own Mathlib
  version. We do them one at a time, and we delete each build after the extraction.
- A native install of Rocq on Windows.
- Isabelle. The Pool Server has it.
