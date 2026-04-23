// Task Provider for SimplicityHL.
// Integrates with VSCode's "Tasks: Run Task" command for build automation.

import * as vscode from "vscode";
import { getSimcPath } from "./compile";

// Task definition schema - matches taskDefinitions in package.json
export interface SimplicityHLTaskDefinition extends vscode.TaskDefinition {
  type: "simplicityhl";
  command: "compile" | "compile-debug" | "compile-with-witness";
  file?: string;        // Override file to compile (defaults to ${file})
  witnessFile?: string; // Witness file for compile-with-witness
}

// Provides tasks to VSCode's task system
export class SimplicityHLTaskProvider implements vscode.TaskProvider {
  static TaskType = "simplicityhl";
  private tasks: vscode.Task[] | undefined;

  // Called by VSCode to get list of available tasks
  public async provideTasks(): Promise<vscode.Task[]> {
    if (!this.tasks) {
      this.tasks = await this.buildTasks();
    }
    return this.tasks;
  }

  // Called when user runs a task from tasks.json
  public async resolveTask(task: vscode.Task): Promise<vscode.Task | undefined> {
    const definition = task.definition as SimplicityHLTaskDefinition;
    if (definition.type === SimplicityHLTaskProvider.TaskType) {
      return this.createTask(definition);
    }
    return undefined;
  }

  // Build default tasks shown in task picker
  private async buildTasks(): Promise<vscode.Task[]> {
    const tasks: vscode.Task[] = [];

    // Basic compile task
    tasks.push(await this.createTask({
      type: "simplicityhl",
      command: "compile",
    }));

    // Compile with debug symbols
    tasks.push(await this.createTask({
      type: "simplicityhl",
      command: "compile-debug",
    }));

    // Compile with witness
    tasks.push(await this.createTask({
      type: "simplicityhl",
      command: "compile-with-witness",
    }));

    return tasks;
  }

  // Create a VSCode task from our definition
  private async createTask(definition: SimplicityHLTaskDefinition): Promise<vscode.Task> {
    const simcPath = getSimcPath();
    let args: string[] = [];
    let taskName: string;

    // Build command line based on task type
    switch (definition.command) {
      case "compile":
        taskName = "Compile SimplicityHL";
        args = [definition.file || "${file}"];
        break;
      case "compile-debug":
        taskName = "Compile SimplicityHL (Debug)";
        args = [definition.file || "${file}", "--debug"];
        break;
      case "compile-with-witness":
        taskName = "Compile with Witness";
        args = [definition.file || "${file}"];
        args.push("-w");
        if (definition.witnessFile) {
          args.push(definition.witnessFile);
        } else {
          // Default: replace .simf with .wit
          args.push("${file/.simf/.wit/}");
        }
        break;
    }

    const execution = new vscode.ShellExecution(simcPath, args);

    const task = new vscode.Task(
      definition,
      vscode.TaskScope.Workspace,
      taskName,
      "simplicityhl",
      execution,
      "$simplicityhl" // Problem matcher name from package.json
    );

    // Mark as build task so it appears in build task list
    task.group = vscode.TaskGroup.Build;
    task.presentationOptions = {
      reveal: vscode.TaskRevealKind.Always,
      panel: vscode.TaskPanelKind.Shared,
    };

    return task;
  }

}

// Register the task provider with VSCode
export function registerTaskProvider(context: vscode.ExtensionContext): void {
  const taskProvider = vscode.tasks.registerTaskProvider(
    SimplicityHLTaskProvider.TaskType,
    new SimplicityHLTaskProvider()
  );

  context.subscriptions.push(taskProvider);
}
