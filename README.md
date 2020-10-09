# Logical Verification 2020 - Installation Instructions

We have installation instructions for Windows, Linux, and MacOS.
As a backup plan, we will prepare a virtual machine on which
Lean is already installed. Check back soon!

These directions are adapted from the
[leanprover-community](https://leanprover-community.github.io/get_started.html#regular-install)
webpage.

<details><summary>Windows</summary>

## Windows

These instructions are also covered in a [YouTube video](https://www.youtube.com/watch?v=y3GsHIe4wZ4).
This does not include the "Install our Logical Verification Repository" step.

### Get Lean

* Install Git for Windows: https://gitforwindows.org/.
  Accept all default answers during the installation
  (or, if you would like to minimize the installation,
  you may deselect all components on the "Select components"
  question).

* Start the newly installed `Git Bash` by searching for it in the Windows
search bar.

* In Git Bash, run the command `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`.

* Press `[Enter]` to proceed with the installation.

* Run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile`.

* Close Git Bash.


### Get Python

* Download the latest version of python [here](https://www.python.org/downloads/).

* Run the downloaded file (`python-3.x.x.exe`)

* Check `Add Python 3.x to PATH`.

* Choose the default installation.

* Open Git Bash (type `git bash` in the Start Menu)

* Run `which python`
  * The expected output is something like `/c/Users/<user>/AppData/Local/Programs/Python/Pythonxx-xx/python`. In this case, proceed to the next step.
  * If it's something like `/c/Users/<user>/AppData/Local/Microsoft/WindowsApps/python`, then
    * Did you follow the instruction to select `Add Python 3.x to PATH` during the installation?
      * If not, re-run the python installer to uninstall python and try again.
    * Otherwise, you need to disable a Windows setting.
      * Type `manage app execution aliases` into the Windows search prompt (start menu) and open the corresponding System Settings page.
      * There should be two entries `App Installer python.exe` and `App Installer python3.exe`. Ensure that both of these are set to `Off`.
    * Close and reopen Git Bash and restart this step.
  * If it is any other directory, you might have an existing version of Python. Ask the TAs for help.
  * If you get `command not found`, you should add the Python directory to your path. Google how to do this, or ask the TAs.

* Run `cp "$(which python)" "$(which python)"3`. This ensures that we can use the command `python3` to call Python.

* Test whether everything is working by typing `python3 --version` and `pip3 --version`. If both commands give a short output and no error, everything is set up correctly.
  * If `pip3 --version` doesn't give any output, run the command `python3 -m pip install --upgrade pip`, which should fix it.

### Configure Git

* Run `git config --global core.autocrlf input` in Git Bash.


### Install Lean Tools

* in Git Bash, run

```bash
pip3 install mathlibtools
```

### Install and Configure the Editor

1. Install [VS Code](https://code.visualstudio.com/).

2. Launch VS Code.

3. Click on the extension icon ![(image of icon)](img/new-extensions-icon.png)
   (or ![(image of icon)](img/extensions-icon.png) in older versions) in the side bar on the left edge of
   the screen (or press <kbd>Shift</kbd><kbd>Ctrl</kbd><kbd>X</kbd>) and search for `leanprover`.

4. Click "install" (In old versions of VS Code, you might need to click "reload" afterwards)

5. Setup the default shell:
  * If you're using `git bash`, press `ctrl-shift-p` to open the command palette, and type
    `Select Default Shell`, then select `git bash` from the menu.

6. Restart VS Code.

7. Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
   A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
   displayed.


### Install Our Logical Verification Repository

* Close VSCode.

* Open Git Bash.

* In Git Bash, use `cd` to go to the directory you want to place the project in  (a new folder will be created for it at that location). For instance, you can use `cd ~/Documents` to go to your personal Documents folder.

* Run these commands in Git Bash:

```bash
leanproject get blanchette/logical_verification_2020
cd logical_verification_2020
lean --make lean
```

* Launch VSCode.

* In the `File` menu, click `Open Folder`, and choose the folder
  `logical_verification_2019` (not one of its subfolders). If you used
  `~/Documents` above, it will be located in your `Documents` folder.

* In the file explorer on the left-hand side, you will find all
exercises and homework in the `lean` folder,
as we upload them.

* You can retrieve the newest exercises and homework that we upload by clicking the two arrows forming a circle in the bottom left corner.

</details>

<details><summary>Debian/Ubuntu and Derivates</summary>

## Debian/Ubuntu and Derivates

These instructions are also in a [YouTube video](https://www.youtube.com/watch?v=02ff4WrW0FU),
not including the LV details.

### Install Lean

* Open a terminal.

```bash
wget -q https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile
```
(will take some time)


### Install our Logical Verification Repository

* Use `cd` to go to the directory you want to place the project in. (A new
  folder will be created for it at that location.)

```bash
leanproject get blanchette/logical_verification_2020
cd logical_verification_2020
lean --make lean
```

* Launch VScode, either through your application menu or by typing `code`.

* On the main screen, or in the `File` menu, click `Open Folder`, and choose
  the folder `logical_verification_2019` (not one of its subfolders).

* In the file explorer on the left-hand side, you will find all exercises and
  homework in the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by
  clicking the two arrows forming a circle in the bottom left corner.

</details>

<details><summary>Other Linux Distros</summary>

## Other Linux Distros

Follow [these instructions](https://leanprover-community.github.io/install/linux.html) and proceed by the instructions "Install our logical verification repository"
for Debian/Ubunutu above.

</details>

<details><summary>macOS</summary>

## macOS

These instructions are also in a [YouTube video](https://www.youtube.com/watch?v=NOGWsCNm_FY&ab_channel=leanprovercommunity), not including the LV repository details.

### Install Lean

* Open a terminal.


```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_macos.sh)" && source ~/.profile
```
(will take some times)

### Install our Logical Verification Repository

* Open a terminal.

* Use `cd` to go to the directory you want to place the project in  (a new folder will be created for it at that location),
for example you can use `~/Documents`.

```bash
leanproject get blanchette/logical_verification_2020
cd logical_verification_2020
lean --make lean
```

* Open VScode again.

* In the `File` menu, click `Open`, and choose the folder
  `logical_verification_2019` (not one of its subfolders). If you used
  `~/Documents` above, it will be in the `Documents` folder.

* In the file explorer on the left-hand side, you will find all exercises and
  homework in the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by
  clicking the two arrows forming a circle in the bottom left corner.

</details>

<details><summary>Virtual Machine (for Any Operating System)</summary>

## Virtual Machine

Coming soon.

<!-- * Download and install [VirtualBox](https://www.virtualbox.org/).
  (Other virtualization software should also work.)

* Download the virtual machine from
  https://drive.google.com/drive/folders/15R22c3iiYn4a2USkOFU6PvW6KbsS4-B0?usp=sharing.

* Open VirtualBox.

* Import the downloaded file via `File > Import Appliance`.

* Select the `.ova` file you downloaded, click `Continue` and then `Import`.

* Start the virtual machine by selecting `logical_verification_2019` and
  clicking the `Start` button and wait for the system to boot.

* Open VSCode by clicking on the blue ribbon icon on the left.

* If you need the password for the virtual machine at some point, it is
  `love`. -->

</details>