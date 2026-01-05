import { opendir, opendirSync } from "fs";
import * as path from "path";
import { workspace, ExtensionContext } from "vscode";
import * as vscode from "vscode";

import {
	Executable,
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient;

export function activate(context: ExtensionContext) {
	console.log("uwu");
	console.log("owo");

	const fardCommand = vscode.commands.registerCommand("spine-lang.fard", () => {
		vscode.window.showInformationMessage("Jaaj");
		vscode.window.showWarningMessage("Jaaj !!!!!!!!!!");
	});
	context.subscriptions.push(fardCommand);

	const run: Executable = {
		command: "spine",
		args: ["--lsp"],
		options: {
			env: {
				...process.env,
			},
		},
	};

	const serverOptions: ServerOptions = {
		run,
		debug: run,
	};

	const clientOptions: LanguageClientOptions = {
		documentSelector: [{ scheme: "file", language: "spine" }],
		outputChannel: vscode.window.createOutputChannel("Spine Language Server"),
	};

	client = new LanguageClient(
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
	//sstatusBar.backgroundColor = new vscode.ThemeColor('statusBarItem.warningBackground');
	statusBar.show();

	client.onReady().then(() => {
		client.onNotification("window/logMessage", (awa: string) => {
			console.log(awa);
		});
	});

	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
