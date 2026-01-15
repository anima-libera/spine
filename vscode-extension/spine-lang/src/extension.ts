import { error } from "console";
import * as vscode from "vscode";
import * as lsp from "vscode-languageclient/node";

let client: lsp.LanguageClient | null = null;

function getSpineExecutablePath(): string | null {
	var spineExecutablePath: string | undefined =
		vscode.workspace.getConfiguration("spine-lang").get("languageServerPath");
	if (spineExecutablePath == undefined) {
		spineExecutablePath = `${process.env.HOME}/.cargo/bin/spine`;
	}
	if (spineExecutablePath.includes("~")) {
		const home = process.env.HOME;
		if (home == undefined) {
			const errorMessage = `no HOME env variable to use to replace \`~\` in language server path \`${spineExecutablePath}\``;
			vscode.window.showErrorMessage(errorMessage);
			console.error(errorMessage);
			return null;
		}
		spineExecutablePath = spineExecutablePath.replaceAll("~", home);
	}
	return spineExecutablePath;
}

function startOrRestartLanguageServer() {
	if (client != null) {
		client.stop();
		client = null;
	}

	const spineExecutablePath = getSpineExecutablePath();
	if (spineExecutablePath == null) {
		return;
	}

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

	client.onDidChangeState((stateChange) => {
		if (stateChange.newState == lsp.State.Running && client != null) {
			client.onNotification("window/logMessage",  (awa: string) => {
				console.log(awa);
			});
		}
	});

	client.start();
}

export function activate(context: vscode.ExtensionContext) {
	console.log("uwu");
	console.log("owo");

	context.subscriptions.push(vscode.commands.registerCommand("spine-lang.fard", () => {
		vscode.window.showInformationMessage("Jaaj");
		vscode.window.showWarningMessage("Jaaj !!!!!!!!!!");
	}));
	context.subscriptions.push(vscode.commands.registerCommand("spine-lang.restartLanguageServer", () => {
		startOrRestartLanguageServer();
	}));

	startOrRestartLanguageServer();

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
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
