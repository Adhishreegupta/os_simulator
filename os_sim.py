import tkinter as tk
from tkinter import ttk, messagebox
import copy
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

# I. ALGORITHM IMPLEMENTATIONS 

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
    # Non-preemptive SJF
    processes.sort(key=lambda x: x['arrival'])
    completed, time, gantt = [], 0, []
    while len(completed) < len(processes):
        ready = [p for p in processes if p not in completed and p['arrival'] <= time]
        if not ready:
            if [p for p in processes if p not in completed]:
                time += 1
            else:
                break
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
    # Non-preemptive Priority
    processes.sort(key=lambda x: x['arrival'])
    completed, time, gantt = [], 0, []
    while len(completed) < len(processes):
        ready = [p for p in processes if p not in completed and p['arrival'] <= time]
        if not ready:
            if [p for p in processes if p not in completed]:
                time += 1
            else:
                break
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
    working = sorted(copy.deepcopy(processes), key=lambda x: x['arrival'])
    for p in working:
        p['remaining_burst'] = p['burst']
        p['wait_time'] = 0
        p['turn_time'] = 0
        p['last_run'] = p['arrival']
    
    time, gantt, completed = 0, [], 0
    ready_queue = []
    
    while completed < len(working):
        # 1. Add new arrivals to ready queue
        i = 0
        while i < len(working):
            if working[i]['arrival'] <= time and working[i]['remaining_burst'] > 0 and working[i] not in ready_queue:
                ready_queue.append(working[i])
                working.pop(i) 
            else:
                i += 1

        if not ready_queue:
            next_arrival = min([p['arrival'] for p in working if p['remaining_burst'] > 0], default=None)
            if next_arrival is not None:
                time = next_arrival
                continue
            else: 
                break
        
        # 3. Process runs
        p = ready_queue.pop(0)
        run_time = min(quantum, p['remaining_burst'])
        start = time
        time += run_time
        
        p['remaining_burst'] -= run_time
        gantt.append((p['pid'], start, time))
        
        # 4. Add new arrivals that came during the run time
        i = 0
        while i < len(working):
            if working[i]['arrival'] <= time and working[i]['remaining_burst'] > 0 and working[i] not in ready_queue:
                ready_queue.append(working[i])
                working.pop(i)
            else:
                i += 1
        
        # 5. Check completion or re-enqueue
        if p['remaining_burst'] > 0:
            ready_queue.append(p)
        else:
            p['turn_time'] = time - p['arrival']
            p['wait_time'] = p['turn_time'] - p['burst']
            completed += 1
            
    final_procs = []
    for orig_p in processes:
        completion_time = max([end for pid, start, end in gantt if pid == orig_p['pid']], default=0)
        turnaround = completion_time - orig_p['arrival']
        waiting = turnaround - orig_p['burst']

        p_copy = copy.deepcopy(orig_p)
        p_copy['waiting'] = waiting
        p_copy['turnaround'] = turnaround
        final_procs.append(p_copy)
        
    return gantt, final_procs

def fifo_page_replacement(pages, frames):
    memory, faults, history = [], 0, []
    for page in pages:
        is_fault = False
        if page not in memory:
            faults += 1
            is_fault = True
            if len(memory) < frames:
                memory.append(page)
            else:
                memory.pop(0)
                memory.append(page)
        history.append((page, list(memory), is_fault))
    return faults, history

def lru_page_replacement(pages, frames):
    memory, faults, history = [], 0, []
    recent = [] 
    for page in pages:
        is_fault = False
        if page not in memory:
            faults += 1
            is_fault = True
            if len(memory) < frames:
                memory.append(page)
                recent.append(page)
            else:
                lru_page = recent.pop(0)
                victim_index = memory.index(lru_page)
                memory[victim_index] = page
                recent.append(page)
        else:
            recent.remove(page)
            recent.append(page)
            
        history.append((page, list(memory), is_fault))
    return faults, history

def optimal_page_replacement(pages, frames):
    memory, faults, history = [], 0, []
    for i, page in enumerate(pages):
        is_fault = False
        if page not in memory:
            faults += 1
            is_fault = True
            if len(memory) < frames:
                memory.append(page)
            else:
                future = pages[i + 1:]
                indices = []
                for m in memory:
                    try:
                        indices.append(future.index(m))
                    except ValueError:
                        indices.append(float('inf'))
                
                victim = indices.index(max(indices))
                memory[victim] = page
                
        history.append((page, list(memory), is_fault))
    return faults, history


# II. GUI INTEGRATION 

class OSSimulator:
    def __init__(self, root):
        self.root = root
        self.root.title("🛡️ OS Simulator by AlgoVengers 🚀")
        self.root.geometry("1050x780") 
        self.root.configure(bg="#0D1B2A")

        # Define custom colors
        DARK_NAVY = "#0D1B2A"
        MID_BLUE = "#1B2F4C"
        ACCENT_BLUE = "#41A0FF"
        TEXT_LIGHT = "#E0FBFC"
        TEXT_DARK = "#0D1B2A"
        
        # General Styles
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TFrame", background=DARK_NAVY)
        style.configure("TLabel", background=DARK_NAVY, foreground=TEXT_LIGHT, font=("Calibri", 11))
        style.configure("TLabelframe", background=DARK_NAVY, foreground=ACCENT_BLUE, font=("Calibri", 12, "bold"))
        style.configure("TLabelframe.Label", background=DARK_NAVY, foreground=ACCENT_BLUE)

        # Entry/Text Box Style
        style.configure("TEntry", fieldbackground=MID_BLUE, background=MID_BLUE, foreground=TEXT_LIGHT, font=("Consolas", 11), borderwidth=0)
        style.configure("TCombobox", fieldbackground=MID_BLUE, background=MID_BLUE, foreground=TEXT_LIGHT, font=("Consolas", 11), borderwidth=0)
        style.map("TCombobox", fieldbackground=[('readonly', MID_BLUE)])

        # Notebook Tab Style
        style.configure("TNotebook", background=DARK_NAVY, borderwidth=0)
        style.configure("TNotebook.Tab", background=MID_BLUE, foreground=TEXT_LIGHT, font=("Calibri", 11, "bold"), padding=[10, 5])
        style.map("TNotebook.Tab", 
                  background=[('selected', ACCENT_BLUE)], 
                  foreground=[('selected', TEXT_DARK)])

        # Treeview (Results Table) Style
        style.configure("Treeview", background=MID_BLUE, foreground=TEXT_LIGHT, font=("Consolas", 10), fieldbackground=MID_BLUE, borderwidth=0)
        style.configure("Treeview.Heading", background=ACCENT_BLUE, foreground=TEXT_DARK, font=("Calibri", 11, "bold"), relief="flat")
        style.map("Treeview.Heading", background=[('active', ACCENT_BLUE)])
        
        # --- 3D-Style Animated Button ---
        style.configure("Professional.TButton", 
                        font=("Calibri", 12, "bold"),
                        background=ACCENT_BLUE, 
                        foreground=TEXT_DARK,
                        relief="flat",
                        padding=[15, 8, 15, 8], # Initial padding
                        borderwidth=0)
        
        style.map("Professional.TButton",
                  background=[('active', "#60B0FF")], 
                  foreground=[('active', TEXT_DARK)],
                  relief=[('pressed', 'sunken')],
                  padding=[('pressed', [15, 9, 15, 7])]
                 )

        self.create_widgets()

    def create_widgets(self):
        notebook = ttk.Notebook(self.root, style="TNotebook")
        self.cpu_tab = ttk.Frame(notebook, style="TFrame")
        self.mem_tab = ttk.Frame(notebook, style="TFrame")
        notebook.add(self.cpu_tab, text="🧠 CPU Scheduling")
        notebook.add(self.mem_tab, text="💾 Memory Management")
        notebook.pack(expand=1, fill="both", padx=10, pady=10)

        self.build_cpu_tab()
        self.build_mem_tab()

    def build_cpu_tab(self):
        frame = ttk.Frame(self.cpu_tab, padding=15, style="TFrame")
        frame.pack(expand=1, fill="both")

        # Process Input
        input_fr = ttk.LabelFrame(frame, text="Process Input", padding=10)
        input_fr.pack(fill="x", pady=10)
        ttk.Label(input_fr, text="Enter one per line: PID Arrival Burst [Priority] (e.g., P1 0 10 3)").pack(anchor="w")
        self.process_text = tk.Text(input_fr, height=6, bg="#1B2F4C", fg="#E0FBFC", insertbackground="#E0FBFC", font=("Consolas", 11), relief="flat")
        self.process_text.pack(fill="x", pady=5)
        self.process_text.insert("1.0", "P1 0 8 3\nP2 1 4 1\nP3 2 9 4\nP4 3 5 2")

        # Algorithm Settings
        algo_fr = ttk.LabelFrame(frame, text="Algorithm Settings", padding=10)
        algo_fr.pack(fill="x", pady=10)
        
        settings_fr = ttk.Frame(algo_fr, style="TFrame")
        settings_fr.pack(fill="x")
        
        ttk.Label(settings_fr, text="Select Algorithm:").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.cpu_algo = ttk.Combobox(settings_fr, values=["FCFS", "SJF", "Priority", "Round Robin"], style="TCombobox", state="readonly", width=20)
        self.cpu_algo.set("SJF")
        self.cpu_algo.grid(row=0, column=1, padx=5, pady=5, sticky="w")
        
        ttk.Label(settings_fr, text="Time Quantum (for RR):").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.quantum_entry = ttk.Entry(settings_fr, style="TEntry", width=10)
        self.quantum_entry.insert(0, "2")
        self.quantum_entry.grid(row=1, column=1, padx=5, pady=5, sticky="w")
        
        run_btn = ttk.Button(settings_fr, text="▶ RUN SCHEDULING & COMPARE", command=self.run_cpu, style="Professional.TButton")
        run_btn.grid(row=0, column=2, rowspan=2, padx=25, sticky="nswe")
        
        settings_fr.grid_columnconfigure(2, weight=1)

        # Results & Gantt Chart
        result_fr = ttk.LabelFrame(frame, text="Results Table", padding=10)
        result_fr.pack(fill="x", pady=10)

        columns = ("PID", "Arrival", "Burst", "Priority", "Waiting Time", "Turnaround Time")
        self.tree = ttk.Treeview(result_fr, columns=columns, show="headings", selectmode="none", height=6, style="Treeview")
        for col in columns:
            self.tree.heading(col, text=col)
            self.tree.column(col, anchor="center", width=int(1000/len(columns)))
        self.tree.pack(side="top", fill="x")

        self.summary_label = tk.Text(result_fr, height=7, bg="#1B2F4C", fg="#E0FBFC", insertbackground="#E0FBFC", font=("Consolas", 10), relief="flat")
        self.summary_label.pack(fill="x", pady=(5, 0))

        gantt_fr = ttk.LabelFrame(frame, text="Note on Visualization", padding=10)
        gantt_fr.pack(fill="both", expand=1, pady=10)
        
        ttk.Label(gantt_fr, text="A separate pop-up window will appear showing the comparative Gantt charts for all four algorithms (FCFS, SJF, Priority, RR) after clicking 'RUN'. Time units are explicitly marked on the x-axis of each chart.", 
                  wraplength=700, font=("Calibri", 11, "italic")).pack(pady=10, padx=10)
        
        # Placeholder Matplotlib canvas
        self.figure = plt.Figure(figsize=(8, 2.5), facecolor="#0D1B2A")
        self.ax = self.figure.add_subplot(111)
        self.ax.set_facecolor("#0D1B2A")
        self.ax.set_xticks([])
        self.ax.set_yticks([])
        self.canvas = FigureCanvasTkAgg(self.figure, master=gantt_fr)
        self.canvas.get_tk_widget().pack(fill="both", expand=1)

    def build_mem_tab(self):
        frame = ttk.Frame(self.mem_tab, padding=15, style="TFrame")
        frame.pack(expand=1, fill="both")

        # Memory Input
        input_fr = ttk.LabelFrame(frame, text="Page Replacement Input", padding=10)
        input_fr.pack(fill="x", pady=10)
        ttk.Label(input_fr, text="Reference String (comma separated page numbers, e.g., 1,2,3,4,1,5):").pack(anchor="w")
        self.ref_entry = ttk.Entry(input_fr, style="TEntry")
        self.ref_entry.pack(fill="x", pady=3)
        self.ref_entry.insert(0, "7,0,1,2,0,3,0,4,2,3,0,3,2,1,2,0,1,7,0,1")
        
        ttk.Label(input_fr, text="Number of Frames:").pack(anchor="w", pady=(10,3))
        self.frame_entry = ttk.Entry(input_fr, style="TEntry", width=10)
        self.frame_entry.pack(anchor="w", pady=3)
        self.frame_entry.insert(0, "3")

        # Algorithm
        algo_fr = ttk.LabelFrame(frame, text="Algorithm", padding=10)
        algo_fr.pack(fill="x", pady=10)
        
        settings_fr = ttk.Frame(algo_fr, style="TFrame")
        settings_fr.pack(fill="x")
        
        ttk.Label(settings_fr, text="Select Algorithm:").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.mem_algo = ttk.Combobox(settings_fr, values=["FIFO", "LRU", "Optimal"], style="TCombobox", state="readonly", width=15)
        self.mem_algo.set("LRU")
        self.mem_algo.grid(row=0, column=1, padx=5, pady=5, sticky="w")
        
        run_btn = ttk.Button(settings_fr, text="▶ RUN SIMULATION", command=self.run_memory, style="Professional.TButton")
        run_btn.grid(row=0, column=2, padx=25, sticky="e")
        
        settings_fr.grid_columnconfigure(2, weight=1)

        # Output
        out_fr = ttk.LabelFrame(frame, text="Memory Trace & Results", padding=10)
        out_fr.pack(fill="both", expand=1, pady=10)
        
        scrollbar = ttk.Scrollbar(out_fr)
        scrollbar.pack(side="right", fill="y")
        
        self.memory_output = tk.Text(out_fr, height=12, bg="#1B2F4C", fg="#E0FBFC", 
                                     insertbackground="#E0FBFC", font=("Consolas", 10), 
                                     relief="flat", wrap="none", yscrollcommand=scrollbar.set)
        self.memory_output.pack(fill="both", expand=1)
        
        scrollbar.config(command=self.memory_output.yview)
    
    # --- Helper functions ---
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
            
            # 1. Parse Input
            base_processes = []
            for line in text:
                parts = line.split()
                if len(parts) < 3:
                    raise ValueError("Each line must have PID Arrival Burst [Priority].")
                pid, arr, burst = parts[0], int(parts[1]), int(parts[2])
                priority = int(parts[3]) if len(parts) > 3 else 1
                base_processes.append({'pid': pid, 'arrival': arr, 'burst': burst, 'orig_burst': burst, 'priority': priority})

            chosen_algo = self.cpu_algo.get()
            quantum = int(self.quantum_entry.get()) if self.quantum_entry.get().isdigit() and int(self.quantum_entry.get()) > 0 else 2

            # 2. Run All Algorithms on Deep Copies
            procs_fcfs = copy.deepcopy(base_processes)
            gantt_fcfs, procs_fcfs = fcfs_scheduling(procs_fcfs)

            procs_sjf = copy.deepcopy(base_processes)
            gantt_sjf, procs_sjf = sjf_scheduling(procs_sjf)

            procs_prio = copy.deepcopy(base_processes)
            gantt_prio, procs_prio = priority_scheduling(procs_prio)

            procs_rr = copy.deepcopy(base_processes)
            gantt_rr, procs_rr = round_robin(procs_rr, quantum)

            all_results = {
                "FCFS": {"gantt": gantt_fcfs, "procs": procs_fcfs, "avg": self.compute_avg_metrics(procs_fcfs)},
                "SJF": {"gantt": gantt_sjf, "procs": procs_sjf, "avg": self.compute_avg_metrics(procs_sjf)},
                "Priority": {"gantt": gantt_prio, "procs": procs_prio, "avg": self.compute_avg_metrics(procs_prio)},
                "Round Robin": {"gantt": gantt_rr, "procs": procs_rr, "avg": self.compute_avg_metrics(procs_rr)},
            }

            # 3. Display Detailed results for the Chosen Algorithm in the Treeview
            chosen_key = chosen_algo
            self.display_cpu_results(all_results[chosen_key]['gantt'], all_results[chosen_key]['procs'], chosen_key)

            # 4. Show Comparative Gantts and Analysis
            self.show_comparative_gantt(all_results, quantum)

        except Exception as e:
            messagebox.showerror("CPU Scheduling Error", str(e))

    def display_cpu_results(self, gantt, procs, algo):
        # Clear Treeview
        for item in self.tree.get_children():
            self.tree.delete(item)
            
        # Populate Treeview
        for p in procs:
            priority = p.get('priority', 1)
            self.tree.insert("", "end", values=(p['pid'], p['arrival'], p['burst'], priority, f"{p['waiting']:.2f}", f"{p['turnaround']:.2f}"))

        # Clear and prepare Text Summary box
        self.summary_label.delete(1.0, tk.END)
        avg_wait, avg_turn = self.compute_avg_metrics(procs)
        
        self.summary_label.insert(tk.END, f"Detailed Metrics for: {algo}\n", 'title')
        self.summary_label.insert(tk.END, f"---------------------------------------------------\n")
        self.summary_label.insert(tk.END, f"Average Waiting Time: {avg_wait:.2f}\n")
        self.summary_label.insert(tk.END, f"Average Turnaround Time: {avg_turn:.2f}\n")
        self.summary_label.insert(tk.END, f"Total Execution Time: {gantt[-1][2] if gantt else 0}\n")
        self.summary_label.insert(tk.END, f"---------------------------------------------------\n")
        
        self.summary_label.tag_config('title', foreground='#41A0FF', font=('Consolas', 11, 'bold'))

    # --- show_comparative_gantt with explicit time marks ---
    def show_comparative_gantt(self, all_results, quantum):
        DARK_NAVY = "#0D1B2A"
        MID_BLUE = "#1B2F4C"
        TEXT_LIGHT = "#E0FBFC"

        algos = ["FCFS", "SJF", "Priority", "Round Robin"]
        fig, axs = plt.subplots(len(algos), 1, figsize=(10, 2.8 * len(algos)), sharex=True, facecolor=DARK_NAVY)
        
        pid_colors = {
            'P1': '#FF5733', 'P2': '#33FF57', 'P3': '#3357FF', 'P4': '#FF33A1', 
            'P5': '#33FFF6', 'P6': '#F6FF33', 'P7': '#A133FF', 'P8': '#FF8D33'
        }
        
        # 1. Collect all unique time points from all algorithms
        all_time_points = set()
        for algo in algos:
            gantt = all_results[algo]['gantt']
            for _, start, end in gantt:
                all_time_points.add(start)
                all_time_points.add(end)
        
        # Create a sorted list of unique time points for the x-axis ticks
        x_ticks = sorted(list(all_time_points))
        
        # 2. Iterate and draw each chart
        for ax, algo in zip(axs, algos):
            gantt = all_results[algo]['gantt']
            
            # Styling the subplot
            ax.set_facecolor(MID_BLUE)
            ax.tick_params(axis='x', colors=TEXT_LIGHT)
            ax.spines['bottom'].set_color(TEXT_LIGHT)
            ax.spines['left'].set_color(TEXT_LIGHT)
            ax.set_title(f"Algorithm: {algo}", color=TEXT_LIGHT, fontsize=11)
            
            # Set the explicit time ticks and gridlines
            ax.set_xticks(x_ticks)
            ax.set_xlim(0, max(x_ticks, default=0))
            ax.grid(axis='x', linestyle='--', alpha=0.5, color=TEXT_LIGHT, linewidth=0.5)

            # Drawing the bars and labels
            for pid, start, end in gantt:
                color = pid_colors.get(pid, '#CCCCCC')
                ax.barh(0, end - start, left=start, height=0.6, color=color, edgecolor='white', linewidth=1)
                ax.text(start + (end - start)/2, 0, pid, ha='center', va='center', color='black', fontweight='bold', fontsize=9)
            
            ax.set_yticks([])
            ax.set_ylim(-1, 1)

        # X label on bottom
        axs[-1].set_xlabel("Time (Units)", color=TEXT_LIGHT, fontsize=12, fontweight='bold')
        
        # Main title
        fig.suptitle(f"CPU Scheduling Comparison (RR Quantum: {quantum})", color=TEXT_LIGHT, fontsize=16, fontweight='bold')
        fig.tight_layout(rect=[0, 0.03, 1, 0.95])
        
        plt.show() # Display the comparative pop-up

        # Append comparative metrics and pick best algorithm
        metrics_summary = []
        for algo in algos:
            avg_wait, avg_turn = all_results[algo]['avg']
            metrics_summary.append((algo, avg_wait, avg_turn))

        metrics_sorted = sorted(metrics_summary, key=lambda x: (x[1], x[2]))
        best_algo, best_wait, best_turn = metrics_sorted[0]

        # Display comparative summary in the Summary Textbox
        self.summary_label.insert(tk.END, "\nComparative Analysis:\n", 'title')
        self.summary_label.insert(tk.END, f"{'Algorithm':<15}{'Avg Wait':<12}{'Avg Turnaround':<16}\n")
        self.summary_label.insert(tk.END, "-"*45 + "\n")
        for algo, aw, at in metrics_summary:
            self.summary_label.insert(tk.END, f"{algo:<15}{aw:<12.2f}{at:<16.2f}\n")
        self.summary_label.insert(tk.END, "-"*45 + "\n")
        self.summary_label.insert(tk.END, f"RECOMMENDED ALGORITHM: {best_algo}\n", 'recommend')
        self.summary_label.insert(tk.END, f"Reason: Lowest Average Waiting Time ({best_wait:.2f}).\n")
        
        self.summary_label.tag_config('recommend', foreground='#33FF57', font=('Consolas', 11, 'bold'))

    # --- Memory functions ---
    def run_memory(self):
        try:
            ref_string = self.ref_entry.get().replace(' ', '')
            pages = list(map(int, ref_string.split(',')))
            frames = int(self.frame_entry.get())
            algo = self.mem_algo.get()
            
            if frames <= 0: raise ValueError("Frames must be a positive integer.")
            if not pages: raise ValueError("Reference string cannot be empty.")
            
            if algo == "FIFO": faults, history = fifo_page_replacement(pages, frames)
            elif algo == "LRU": faults, history = lru_page_replacement(pages, frames)
            elif algo == "Optimal": faults, history = optimal_page_replacement(pages, frames)
            
            self.display_memory_results(history, faults, algo, frames)
            
        except Exception as e:
            messagebox.showerror("Memory Management Error", str(e))

    def display_memory_results(self, history, faults, algo, frames):
        self.memory_output.delete(1.0, tk.END)
        
        frame_headers = [f"F{i+1}" for i in range(frames)]
        header = f"{'Step':<6}{'Page':<8}{'Fault':<8}" + "".join(f"{h:<8}" for h in frame_headers) + "\n"
        self.memory_output.insert(tk.END, header, 'header')
        self.memory_output.insert(tk.END, "-"* (6 + 8 + 8 + frames*8) + "\n")
        
        for i, (page, state, is_fault) in enumerate(history):
            fault_status = "FAULT (X)" if is_fault else "HIT (✓)"
            
            frame_output = []
            for j in range(frames):
                frame_output.append(f"{state[j] if j < len(state) else '-':<8}")
            
            line = f"{i+1:<6}{page:<8}{fault_status:<8}" + "".join(frame_output) + "\n"
            
            tag = 'fault' if is_fault else 'hit'
            self.memory_output.insert(tk.END, line, tag)

        self.memory_output.insert(tk.END, "-"* (6 + 8 + 8 + frames*8) + "\n")
        self.memory_output.insert(tk.END, f"Algorithm: {algo}\n", 'summary')
        self.memory_output.insert(tk.END, f"Total Page Faults: {faults}\n", 'summary')
        
        self.memory_output.tag_config('header', foreground='#41A0FF', font=('Consolas', 10, 'bold'))
        self.memory_output.tag_config('fault', foreground='#FF6347')
        self.memory_output.tag_config('hit', foreground='#33FF57') 
        self.memory_output.tag_config('summary', foreground='#E0FBFC', font=('Consolas', 11, 'bold'))

# MAIN EXECUTION

if __name__ == "__main__":
    root = tk.Tk()
    OSSimulator(root)
    root.mainloop()
