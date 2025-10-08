import tkinter as tk
from tkinter import ttk, messagebox
import matplotlib.pyplot as plt
import copy

def fcfs_scheduling(processes):
    processes.sort(key=lambda x: x['arrival'])
    time, gantt = 0, []
    for p in processes:
        if time < p['arrival']:
            time = p['arrival']
        start, finish = time, time + p['burst']
        gantt.append((p['pid'], start, finish))
        time += p['burst']
        p['waiting'] = start - p['arrival']
        p['turnaround'] = finish - p['arrival']
    return gantt, processes

def sjf_scheduling(processes):
    processes.sort(key=lambda x: x['arrival'])
    completed, time, gantt = [], 0, []
    while len(completed) < len(processes):
        ready = [p for p in processes if p not in completed and p['arrival'] <= time]
        if not ready:
            time += 1
            continue
        p = min(ready, key=lambda x: x['burst'])
        start, finish = time, time + p['burst']
        gantt.append((p['pid'], start, finish))
        time = finish
        p['waiting'] = start - p['arrival']
        p['turnaround'] = finish - p['arrival']
        completed.append(p)
    return gantt, processes

def priority_scheduling(processes):
    processes.sort(key=lambda x: x['arrival'])
    completed, time, gantt = [], 0, []
    while len(completed) < len(processes):
        ready = [p for p in processes if p not in completed and p['arrival'] <= time]
        if not ready:
            time += 1
            continue
        p = min(ready, key=lambda x: x['priority'])
        start, finish = time, time + p['burst']
        gantt.append((p['pid'], start, finish))
        time = finish
        p['waiting'] = start - p['arrival']
        p['turnaround'] = finish - p['arrival']
        completed.append(p)
    return gantt, processes

def round_robin(processes, quantum):
    # make a deep copy of bursts since RR mutates burst
    queue = sorted(processes, key=lambda x: x['arrival'])
    # create a working copy of each process to mutate burst safely
    working = [{'pid': p['pid'], 'arrival': p['arrival'], 'burst': p['burst'], 'orig_burst': p['orig_burst'], 'priority': p.get('priority',1)} for p in queue]
    time, gantt = 0, []
    waiting, turnaround = {}, {}
    ready = []
    idx = 0
    # Use queue and ready lists similar to typical RR simulation
    while working or ready:
        while working and working[0]['arrival'] <= time:
            ready.append(working.pop(0))
        if not ready:
            # if no ready processes, jump to next arrival if exists
            if working:
                time = working[0]['arrival']
                continue
            else:
                break
        p = ready.pop(0)
        start = time
        run_time = min(quantum, p['burst'])
        time += run_time
        gantt.append((p['pid'], start, time))
        p['burst'] -= run_time
        # enqueue any new arrivals that came during the run
        while working and working[0]['arrival'] <= time:
            ready.append(working.pop(0))
        if p['burst'] > 0:
            ready.append(p)
        else:
            turnaround[p['pid']] = time - p['arrival']
            waiting[p['pid']] = turnaround[p['pid']] - p['orig_burst']
    # prepare final processes list to include waiting/turnaround for display
    final_procs = []
    for p in processes:
        pid = p['pid']
        p_copy = copy.deepcopy(p)
        p_copy['waiting'] = waiting.get(pid, 0)
        p_copy['turnaround'] = turnaround.get(pid, p_copy['orig_burst'] + max(0, p_copy['arrival']))  # fallback
        final_procs.append(p_copy)
    return gantt, final_procs


def fifo_page_replacement(pages, frames):
    memory, faults, history = [], 0, []
    for page in pages:
        if page not in memory:
            faults += 1
            if len(memory) < frames:
                memory.append(page)
            else:
                memory.pop(0)
                memory.append(page)
        history.append((page, list(memory)))
    return faults, history

def lru_page_replacement(pages, frames):
    memory, faults, recent, history = [], 0, [], []
    for page in pages:
        if page not in memory:
            faults += 1
            if len(memory) < frames:
                memory.append(page)
            else:
                lru_page = recent.pop(0)
                memory[memory.index(lru_page)] = page
        else:
            if page in recent: recent.remove(page)
        recent.append(page)
        history.append((page, list(memory)))
    return faults, history

def optimal_page_replacement(pages, frames):
    memory, faults, history = [], 0, []
    for i, page in enumerate(pages):
        if page not in memory:
            faults += 1
            if len(memory) < frames:
                memory.append(page)
            else:
                future = pages[i + 1:]
                indices = [future.index(m) if m in future else float('inf') for m in memory]
                victim = indices.index(max(indices))
                memory[victim] = page
        history.append((page, list(memory)))
    return faults, history

# ==========================================================
# Gaming-Themed GUI (no GUI changes)
# ==========================================================
class OSSimulator:
    def __init__(self, root):
        self.root = root
        self.root.title("🎮  OS Simulator")
        self.root.geometry("980x720")
        self.root.configure(bg="black")

        # Style
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TLabel", background="black", foreground="#00ffea", font=("Arial", 12))
        style.configure("TButton", font=("Press Start 2P", 12, "bold"), background="#050e10", foreground="white")
        style.map("TButton", background=[('active', "#b3088e")])
        style.configure("TCombobox", fieldbackground="#111111", background="#050e10", foreground="#00ffea", font=("Press Start 2P", 12))
        style.map("TCombobox", fieldbackground=[('readonly', '#111111')], background=[('readonly', '#050e10')], foreground=[('readonly', '#00ffea')])

        # Black theme for notebook and frames
        style.configure("TNotebook", background="black", borderwidth=0)
        style.configure("TNotebook.Tab", background="black", foreground="#00ffea", lightcolor="black", borderwidth=1)
        style.map("TNotebook.Tab", background=[("selected", "#111111")])
        style.configure("Black.TFrame", background="black")

        # Tabs
        tab_control = ttk.Notebook(root)
        self.cpu_tab = ttk.Frame(tab_control, style="Black.TFrame")
        self.mem_tab = ttk.Frame(tab_control, style="Black.TFrame")
        tab_control.add(self.cpu_tab, text='🧠 CPU Scheduling')
        tab_control.add(self.mem_tab, text='💾 Memory Management')
        tab_control.pack(expand=1, fill='both')

        self.cpu_ui()
        self.memory_ui()

    def cpu_ui(self):
        frame = ttk.Frame(self.cpu_tab, padding=10, style="Black.TFrame")
        frame.pack(fill='both', expand=True)

        ttk.Label(frame, text="Enter Processes (PID Arrival Burst Priority):").pack(anchor='w', pady=5)
        self.process_text = tk.Text(frame, height=6, width=70, bg="black", fg="#00ff00", insertbackground="#00ff00", font=("Courier New", 12))
        self.process_text.pack(pady=5)

        ttk.Label(frame, text="Select Algorithm:").pack(anchor='w', pady=5)
        self.cpu_algo = ttk.Combobox(frame, values=["FCFS", "SJF", "Priority", "Round Robin"], state="readonly")
        self.cpu_algo.set("FCFS")
        self.cpu_algo.pack(pady=5)

        ttk.Label(frame, text="Time Quantum (Round Robin):").pack(anchor='w', pady=5)
        self.quantum_entry = tk.Entry(frame, width=10, font=("Press Start 2P", 12), bg="black", fg="#11C6DA", insertbackground="#00ff00")
        self.quantum_entry.insert(0, "2")
        self.quantum_entry.pack(pady=5)

        ttk.Button(frame, text="▶ Run Scheduling", command=self.run_cpu).pack(pady=10)

        self.cpu_output = tk.Text(frame, height=14, width=95, bg="black", fg="#11C6DA", font=("Courier New", 11, "bold"))
        self.cpu_output.pack(pady=10)

    def memory_ui(self):
        frame = ttk.Frame(self.mem_tab, padding=10, style="Black.TFrame")
        frame.pack(fill='both', expand=True)

        ttk.Label(frame, text="Enter Reference String (comma separated):").pack(anchor='w', pady=5)
        self.ref_entry = tk.Entry(frame, width=70, font=("Press Start 2P", 12), bg="black", fg="#00ffff", insertbackground="#00ffff")
        self.ref_entry.pack(pady=5)

        ttk.Label(frame, text="Number of Frames:").pack(anchor='w', pady=5)
        self.frame_entry = tk.Entry(frame, width=10, font=("Press Start 2P", 12), bg="black", fg="#00ffff", insertbackground="#00ffff")
        self.frame_entry.pack(pady=5)

        ttk.Label(frame, text="Select Algorithm:").pack(anchor='w', pady=5)
        self.mem_algo = ttk.Combobox(frame, values=["FIFO", "LRU", "Optimal"], state="readonly")
        self.mem_algo.set("FIFO")
        self.mem_algo.pack(pady=5)

        ttk.Button(frame, text="▶ Run Simulation", command=self.run_memory).pack(pady=10)

        self.memory_output = tk.Text(frame, height=15, width=95, bg="black", fg="#00ffff", font=("Courier New", 11, "bold"))
        self.memory_output.pack(pady=10)

    # --- new helper to compute avg metrics ---
    def compute_avg_metrics(self, procs):
        n = len(procs)
        total_wait = sum(p.get('waiting', 0) for p in procs)
        total_turn = sum(p.get('turnaround', 0) for p in procs)
        avg_wait = total_wait / n if n else 0
        avg_turn = total_turn / n if n else 0
        return avg_wait, avg_turn

    def run_cpu(self):
        try:
            text = self.process_text.get("1.0", "end-1c").strip().splitlines()
            if not text:
                raise ValueError("Please enter processes.")
            # parse input
            base_processes = []
            for line in text:
                parts = line.split()
                if len(parts) < 3:
                    raise ValueError("Each line must have PID Arrival Burst [Priority].")
                pid, arr, burst = parts[0], int(parts[1]), int(parts[2])
                priority = int(parts[3]) if len(parts) > 3 else 1
                base_processes.append({'pid': pid, 'arrival': arr, 'burst': burst, 'orig_burst': burst, 'priority': priority})

            chosen_algo = self.cpu_algo.get()
            quantum = int(self.quantum_entry.get()) if self.quantum_entry.get() else 2

            # Run all algorithms on deep copies so original input isn't mutated
            procs_fcfs = copy.deepcopy(base_processes)
            gantt_fcfs, procs_fcfs = fcfs_scheduling(procs_fcfs)
            avg_fcfs = self.compute_avg_metrics(procs_fcfs)

            procs_sjf = copy.deepcopy(base_processes)
            gantt_sjf, procs_sjf = sjf_scheduling(procs_sjf)
            avg_sjf = self.compute_avg_metrics(procs_sjf)

            procs_prio = copy.deepcopy(base_processes)
            gantt_prio, procs_prio = priority_scheduling(procs_prio)
            avg_prio = self.compute_avg_metrics(procs_prio)

            procs_rr = copy.deepcopy(base_processes)
            gantt_rr, procs_rr = round_robin(procs_rr, quantum)
            avg_rr = self.compute_avg_metrics(procs_rr)

            all_results = {
                "FCFS": {"gantt": gantt_fcfs, "procs": procs_fcfs, "avg": avg_fcfs},
                "SJF": {"gantt": gantt_sjf, "procs": procs_sjf, "avg": avg_sjf},
                "Priority": {"gantt": gantt_prio, "procs": procs_prio, "avg": avg_prio},
                "Round Robin": {"gantt": gantt_rr, "procs": procs_rr, "avg": avg_rr},
            }

            # Display results for the chosen algorithm in existing output box
            chosen_key = chosen_algo
            self.display_cpu_results(all_results[chosen_key]['gantt'], all_results[chosen_key]['procs'], chosen_key)

            # Show comparative gantts and analysis
            self.show_comparative_gantt(all_results, quantum)

        except Exception as e:
            messagebox.showerror("Error", str(e))

    def display_cpu_results(self, gantt, procs, algo):
        self.cpu_output.delete(1.0, tk.END)
        total_wait = sum(p['waiting'] for p in procs)
        total_turn = sum(p['turnaround'] for p in procs)
        avg_wait = total_wait / len(procs) if procs else 0
        avg_turn = total_turn / len(procs) if procs else 0
        self.cpu_output.insert(tk.END,
                               f"{'PID':<8}{'Arrival':<10}{'Burst':<10}{'Priority':<10}{'Wait':<10}{'Turnaround':<12}\n")
        self.cpu_output.insert(tk.END, "-" * 70 + "\n")
        for p in procs:
            self.cpu_output.insert(tk.END,
                                   f"{p['pid']:<8}{p['arrival']:<10}{p['orig_burst']:<10}{p.get('priority',1):<10}{p['waiting']:<10}{p['turnaround']:<12}\n")
        self.cpu_output.insert(tk.END, "-" * 70 + "\n")
        self.cpu_output.insert(tk.END,
                               f"Algorithm: {algo}\nAverage Waiting Time: {avg_wait:.2f}\nAverage Turnaround Time: {avg_turn:.2f}\n\n")

    def show_comparative_gantt(self, all_results, quantum):
        # Build comparative figure with 4 subplots (one per algorithm)
        algos = ["FCFS", "SJF", "Priority", "Round Robin"]
        fig, axs = plt.subplots(len(algos), 1, figsize=(10, 2.4 * len(algos)), sharex=True)
        colors = ['#ff0066', "#2200ff", "#00c8ff", "#00ff15", "#eeff33", "#ff4733"]
        for ax, algo in zip(axs, algos):
            gantt = all_results[algo]['gantt']
            for i, (pid, start, end) in enumerate(gantt):
                ax.barh(algo, end - start, left=start, color=colors[i % len(colors)])
                ax.text(start + (end - start)/2, 0, pid, ha='center', va='center', color='white', fontweight='bold', fontsize=9)
            ax.set_ylabel("")
            ax.set_yticks([])
            ax.set_title(f"{algo} Gantt")
            ax.grid(axis='x', linestyle='--', alpha=0.3)

        # X label on bottom
        axs[-1].set_xlabel("Time", fontsize=12, fontweight='bold')
        fig.suptitle(f"Gantt Chart Comparison (RR quantum={quantum})", fontsize=14, fontweight='bold')
        fig.tight_layout(rect=[0, 0.03, 1, 0.95])
        plt.show()

        # After showing charts, append comparative metrics and pick best algorithm
        metrics_summary = []
        for algo in algos:
            avg_wait, avg_turn = all_results[algo]['avg']
            metrics_summary.append((algo, avg_wait, avg_turn))

        # Determine best: min avg waiting, tie-breaker min avg turnaround
        metrics_sorted = sorted(metrics_summary, key=lambda x: (x[1], x[2]))
        best_algo, best_wait, best_turn = metrics_sorted[0]

        # Display comparative summary in cpu_output
        self.cpu_output.insert(tk.END, "Comparative Analysis:\n")
        self.cpu_output.insert(tk.END, f"{'Algorithm':<15}{'Avg Wait':<12}{'Avg Turnaround':<16}\n")
        self.cpu_output.insert(tk.END, "-"*45 + "\n")
        for algo, aw, at in metrics_summary:
            self.cpu_output.insert(tk.END, f"{algo:<15}{aw:<12.2f}{at:<16.2f}\n")
        self.cpu_output.insert(tk.END, "-"*45 + "\n")
        self.cpu_output.insert(tk.END, f"Recommended (best) Algorithm: {best_algo}\n")
        self.cpu_output.insert(tk.END, f"Reason: Lowest average waiting time ({best_wait:.2f}); turnaround {best_turn:.2f}.\n")

    def run_memory(self):
        try:
            pages = list(map(int, self.ref_entry.get().split(',')))
            frames = int(self.frame_entry.get())
            algo = self.mem_algo.get()
            if algo == "FIFO": faults, history = fifo_page_replacement(pages, frames)
            elif algo == "LRU": faults, history = lru_page_replacement(pages, frames)
            elif algo == "Optimal": faults, history = optimal_page_replacement(pages, frames)
            self.display_memory_results(history, faults, algo)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def display_memory_results(self, history, faults, algo):
        self.memory_output.delete(1.0, tk.END)
        self.memory_output.insert(tk.END, f"{'Step':<6}{'Page':<8}{'Frames':<30}\n")
        self.memory_output.insert(tk.END, "-"*50+"\n")
        for i, (page, state) in enumerate(history):
            frames = ", ".join(map(str, state))
            self.memory_output.insert(tk.END, f"{i+1:<6}{page:<8}{frames:<30}\n")
        self.memory_output.insert(tk.END, "-"*50+"\n")
        self.memory_output.insert(tk.END, f"Algorithm: {algo}\nTotal Page Faults: {faults}\n")

# ==========================================================
# MAIN
# ==========================================================
if __name__ == "__main__":
    root = tk.Tk()
    OSSimulator(root)
    root.mainloop()
