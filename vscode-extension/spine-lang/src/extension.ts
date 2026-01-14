import * as vscode from "vscode";
import * as lsp from "vscode-languageclient/node";

let client: lsp.LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	console.log("uwu");
	console.log("owo");

	const fardCommand = vscode.commands.registerCommand("spine-lang.fard", () => {
		vscode.window.showInformationMessage("Jaaj");
		vscode.window.showWarningMessage("Jaaj !!!!!!!!!!");
	});
	context.subscriptions.push(fardCommand);

	const spineExecutablePath = process.env.HOME + "/.cargo/bin/spine"
	const runLanguageServer: lsp.Executable = {
		command: spineExecutablePath,
		args: ["--lsp"],
		options: {
			env: {
				...process.env,
			},
		},
	};

	const serverOptions: lsp.ServerOptions = {
		run: runLanguageServer,
		debug: runLanguageServer,
	};
	const clientOptions: lsp.LanguageClientOptions = {
		documentSelector: [{ scheme: "file", language: "spine" }],
		outputChannel: vscode.window.createOutputChannel("Spine Language Server"),
	};
	client = new lsp.LanguageClient(
		"spine-language-server",
		"Spine Language Server",
		serverOptions,
		clientOptions
	);

	const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 1);
	statusBar.text = "Spine !!!!!";
	statusBar.tooltip = new vscode.MarkdownString(
		// We do a little testing.
		"# nyo way!!¡\n" +
		"[way?](command:spine-lang.fard \"Does something truly amazing\")\n" +
		"\n---\n\n" +
		"- UwU\n" +
		"- OwO $(terminal) $(terminal) $(terminal) $(terminal) $(terminal) $(loading~spin)"
	);
	statusBar.tooltip.isTrusted = true;
	statusBar.tooltip.supportThemeIcons = true;
	statusBar.command = "spine-lang.fard";
	//statusBar.backgroundColor = new vscode.ThemeColor('statusBarItem.warningBackground');
	statusBar.show();

	client.onDidChangeState((stateChange) => {
		if (stateChange.newState == lsp.State.Running) {
			client.onNotification("window/logMessage",  (awa: string) => {
				console.log(awa);
			});
		}
	});

	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
