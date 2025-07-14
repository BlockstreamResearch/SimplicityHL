# SimplicityHL extension for VSCode

VSCode extension that provides syntax highlighting for the [SimplicityHL](https://docs.simplicity-lang.org/) programming language.

## Features

- Syntax highlighting for .simf files
- Basic language configuration (brackets, comments)

## Installation

Install Node.js (v14 or later recommended).

### Local Installation

1. Clone this repository
2. Navigate to the extension directory:
   ```bash
   cd vscode
   ```
3. Install dependencies:
   ```bash
   npm install
   ```
4. Package the extension:
   ```bash
   npm install -g @vscode/vsce
   vsce package
   ```
   This will create a `.vsix` file in the current directory.

5. Install the extension in VSCode:
   - Launch VS Code
   - Go to the Extensions view (Ctrl+Shift+X)
   - Click on the "..." menu in the top-right of the Extensions view
   - Select "Install from VSIX..."
   - Navigate to and select the `.vsix` file you created

### Alternative Installation Method

You can also install the extension directly from the source code:

1. Copy the `vscode` folder (rename it if necessary) to your VSCode extensions directory:
   - Windows: `%USERPROFILE%\.vscode\extensions`
   - macOS/Linux: `~/.vscode/extensions`

2. Restart VSCode

## Development

1. Clone this repository and cd into `vscode` directory
2. Run `npm install`
3. Open the project in VS Code
4. Press F5 to start debugging (this will launch a new VSCode window with the extension loaded)
5. Make changes to the extension
6. Reload the debugging window to see your changes (Ctrl+R or Cmd+R)

### Reloading the Extension During Development

When making changes to the extension, you can reload it without uninstalling and reinstalling:

1. **Using the Command Palette**:
   - Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS)
   - Type "Developer: Reload Window" and select it

2. **Using keyboard shortcut**:
   - Press `Ctrl+R` (or `Cmd+R` on macOS)

3. **For extensions installed from folder**:
   - Make your changes to the extension files
   - Run the "Developer: Reload Window" command as described above
   - VSCode will reload with the updated extension

4. **For more substantial changes**:
   - If you've made significant changes to the extension's structure or manifest
   - You may need to restart VSCode completely (close and reopen)
   - In some cases, you might need to run the command "Developer: Restart Extension Host"
