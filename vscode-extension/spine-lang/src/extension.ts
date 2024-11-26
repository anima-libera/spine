import * as vscode from 'vscode';

// This method is called when your extension is activated
export function activate(context: vscode.ExtensionContext) {
	console.log('uwu');

	// The command has been defined in the package.json file
	// The commandId parameter must match the command field in package.json
	const disposable = vscode.commands.registerCommand('spine-lang.fard', () => {
		vscode.window.showInformationMessage('Jaaj');
		vscode.window.showWarningMessage('Jaaj !!!!!!!!!!');
	});

	context.subscriptions.push(disposable);
}

export function deactivate() {}
