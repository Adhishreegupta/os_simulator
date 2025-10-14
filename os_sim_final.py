import tkinter as tk
from tkinter import ttk, messagebox
import copy
import matplotlib
matplotlib.use('TkAgg')
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib import cm
from matplotlib.animation import FuncAnimation

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
    
    # Track original processes by PID for final metrics calculation
    orig_procs_map = {p['pid']: p for p in working}
    
    # Store dynamic process state
    dynamic_procs = {p['pid']: p for p in working}
    
    while completed < len(working):
        # Add newly arrived processes to ready queue
        i = 0
        while i < len(working):
            p = working[i]
            if p['arrival'] <= time and p['remaining_burst'] > 0 and p not in ready_queue:
                ready_queue.append(p)
                working.pop(i) 
            else:
                i += 1

        if not ready_queue:
            # Find the next process arrival time to jump to
            next_arrival = min([p['arrival'] for p in working if p['remaining_burst'] > 0], default=None)
            if next_arrival is not None:
                time = next_arrival
                continue
            else: 
                # No more processes left
                break
        
        p = ready_queue.pop(0)
        run_time = min(quantum, p['remaining_burst'])
        start = time
        time += run_time
        
        p['remaining_burst'] -= run_time
        gantt.append((p['pid'], start, time))
        
        # Add processes that arrive during the execution of 'p'
        i = 0
        while i < len(working):
            proc_i = working[i]
            if proc_i['arrival'] <= time and proc_i['remaining_burst'] > 0 and proc_i not in ready_queue:
                ready_queue.append(proc_i)
                working.pop(i)
            else:
                i += 1
        
        if p['remaining_burst'] > 0:
            ready_queue.append(p)
        else:
            p['turn_time'] = time - p['arrival']
            p['wait_time'] = p['turn_time'] - p['burst']
            completed += 1
            
    final_procs = []
    for orig_p in processes:
        # Find all execution segments for the process
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


# II. ANIMATED PROGRESS INDICATOR

class AnimatedProgress(tk.Canvas):
    def __init__(self, parent, **kwargs):
        self.width = kwargs.pop('width', 400)
        self.height = kwargs.pop('height', 6)
        super().__init__(parent, width=self.width, height=self.height,
                        bg='#0D1B2A', highlightthickness=0, **kwargs)
        
        self.progress = 0
        self.is_animating = False
        self.animation_id = None
        
    def start_animation(self):
        self.is_animating = True
        self.progress = 0
        self.animate()
        
    def stop_animation(self):
        self.is_animating = False
        if self.animation_id:
            self.after_cancel(self.animation_id)
        self.delete('all')
        
    def animate(self):
        if not self.is_animating:
            return
            
        self.delete('all')
        
        # Background
        self.create_rectangle(0, 0, self.width, self.height, fill='#1B2F4C', outline='')
        
        # Progress bar
        progress_width = (self.progress / 100) * self.width
        self.create_rectangle(0, 0, progress_width, self.height, fill='#41A0FF', outline='')
        
        # Shine effect
        shine_pos = progress_width - 20
        if shine_pos > 0:
            self.create_rectangle(shine_pos, 0, shine_pos + 20, self.height, 
                                fill='#60B0FF', outline='')
        
        self.progress = (self.progress + 2) % 100
        self.animation_id = self.after(30, self.animate)

# III. Memory Trace Animator for step-by-step visualization
class MemoryTraceAnimator:
    def __init__(self, output_widget, history, pages, frames, algo, root_after_ref):
        self.output = output_widget
        self.history = history
        self.pages = pages
        self.frames = frames
        self.algo = algo
        self.root_after = root_after_ref
        self.current_step = 0
        self.animation_id = None
        self.delay_ms = 400  # Animation step delay

        self.setup_output_initial_state()

    def setup_output_initial_state(self):
        self.output.delete('1.0', tk.END)
        # Configure tags for styling
        self.output.tag_config('title', foreground='#41A0FF', font=('Consolas', 11, 'bold'))
        self.output.tag_config('header', foreground='#60B0FF')
        self.output.tag_config('info', foreground='#E0FBFC')
        self.output.tag_config('faults', foreground='#FF6B6B', font=('Consolas', 10, 'bold'))
        self.output.tag_config('hits', foreground='#51CF66', font=('Consolas', 10, 'bold'))
        self.output.tag_config('table_header', foreground='#FFD700', font=('Consolas', 10, 'bold'))
        self.output.tag_config('separator', foreground='#60B0FF')
        self.output.tag_config('fault_row', foreground='#FFB3B3')
        self.output.tag_config('hit_row', foreground='#B3FFB3')
        # New tag for the currently animated row
        self.output.tag_config('current_step', foreground='#0D1B2A', background='#41A0FF', font=('Consolas', 10, 'bold'))
        self.output.tag_config('footer', foreground='#60B0FF')

        # Initial data display (static)
        self.output.insert(tk.END, "="*70 + "\n", 'header')
        self.output.insert(tk.END, f"🎯 {self.algo} PAGE REPLACEMENT ALGORITHM (ANIMATED TRACE)\n", 'title')
        self.output.insert(tk.END, "="*70 + "\n", 'header')
        self.output.insert(tk.END, f"📄 Reference String: {self.pages}\n", 'info')
        self.output.insert(tk.END, f"🗂️  Number of Frames: {self.frames}\n", 'info')
        self.output.insert(tk.END, "="*70 + "\n\n", 'header')
        
        # Table header
        self.output.insert(tk.END, f"{'Step':<6}{'Page':<8}{'Memory State':<35}{'Status':<10}\n", 'table_header')
        self.output.insert(tk.END, "-"*70 + "\n", 'separator')

    def start_animation(self):
        self.animate_step()

    def stop_animation(self):
        if self.animation_id:
            self.root_after.after_cancel(self.animation_id)
            self.animation_id = None
        self.show_final_metrics()

    def animate_step(self):
        if self.current_step >= len(self.history):
            self.stop_animation()
            return

        # Clear previous highlight
        self.output.tag_remove('current_step', '1.0', tk.END)

        i = self.current_step
        page, mem, fault = self.history[i]
        status = "🔴 FAULT" if fault else "🟢 HIT"
        # Format memory state string with padding for better alignment
        mem_str = str(mem).replace('[', '').replace(']', '').replace(',', ' ').ljust(33)
        
        line = f"{i+1:<6}{page:<8}{mem_str}{status:<10}\n"
        
        # Insert new line
        insert_tag = 'fault_row' if fault else 'hit_row'
        self.output.insert(tk.END, line, (insert_tag, 'current_step')) # Apply both tags
        
        self.output.see(tk.END) # Scroll to end

        self.current_step += 1
        self.animation_id = self.root_after.after(self.delay_ms, self.animate_step)

    def show_final_metrics(self):
        total_pages = len(self.pages)
        total_faults = sum(1 for _, _, fault in self.history if fault)
        
        # Ensure final line is not highlighted
        self.output.tag_remove('current_step', '1.0', tk.END)

        self.output.insert(tk.END, "\n" + "="*70 + "\n", 'header')
        self.output.insert(tk.END, f"❌ Total Page Faults: {total_faults}\n", 'faults')
        self.output.insert(tk.END, f"✅ Hit Ratio: {((total_pages - total_faults) / total_pages * 100):.2f}%\n", 'hits')
        self.output.insert(tk.END, "="*70 + "\n", 'footer')


# IV. GUI INTEGRATION 

class OSSimulator:
    def __init__(self, root):
        self.root = root
        self.root.title("🛡️ OS Simulator by AlgoVengers 🚀")
        self.root.geometry("1100x820") 
        self.root.configure(bg="#0D1B2A")

        # Define custom colors
        self.DARK_NAVY = "#0D1B2A"
        self.MID_BLUE = "#1B2F4C"
        self.ACCENT_BLUE = "#41A0FF"
        self.TEXT_LIGHT = "#E0FBFC"
        self.TEXT_DARK = "#0D1B2A"
        
        # Internal state for the animator
        self.animator = None
        self.MemoryTraceAnimator = MemoryTraceAnimator

        self.setup_styles()
        self.create_widgets()

    def setup_styles(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TFrame", background=self.DARK_NAVY)
        style.configure("TLabel", background=self.DARK_NAVY, foreground=self.TEXT_LIGHT, font=("Calibri", 11))
        style.configure("TLabelframe", background=self.DARK_NAVY, foreground=self.ACCENT_BLUE, font=("Calibri", 12, "bold"))
        style.configure("TLabelframe.Label", background=self.DARK_NAVY, foreground=self.ACCENT_BLUE)
        style.configure("TEntry", fieldbackground=self.MID_BLUE, background=self.MID_BLUE, foreground=self.TEXT_LIGHT, font=("Consolas", 11), borderwidth=0)
        style.configure("TCombobox", fieldbackground=self.MID_BLUE, background=self.MID_BLUE, foreground=self.TEXT_LIGHT, font=("Consolas", 11), borderwidth=0)
        style.map("TCombobox", fieldbackground=[('readonly', self.MID_BLUE)])
        style.configure("TNotebook", background=self.DARK_NAVY, borderwidth=0)
        style.configure("TNotebook.Tab", background=self.MID_BLUE, foreground=self.TEXT_LIGHT, font=("Calibri", 11, "bold"), padding=[15, 8])
        style.map("TNotebook.Tab", 
                  background=[('selected', self.ACCENT_BLUE)], 
                  foreground=[('selected', self.TEXT_DARK)])
        style.configure("Treeview", background=self.MID_BLUE, foreground=self.TEXT_LIGHT, font=("Consolas", 10), fieldbackground=self.MID_BLUE, borderwidth=0)
        style.configure("Treeview.Heading", background=self.ACCENT_BLUE, foreground=self.TEXT_DARK, font=("Calibri", 11, "bold"), relief="flat")
        style.map("Treeview.Heading", background=[('active', self.ACCENT_BLUE)])

    def create_widgets(self):
        # Header with animated title
        header = tk.Frame(self.root, bg=self.DARK_NAVY, height=60)
        header.pack(fill='x', pady=(10, 5))
        header.pack_propagate(False)
        
        title_label = tk.Label(header, text="🛡️ OS SIMULATOR 🚀", 
                              bg=self.DARK_NAVY, fg=self.ACCENT_BLUE,
                              font=("Calibri", 24, "bold"))
        title_label.pack(expand=True)
        
        subtitle = tk.Label(header, text="by AlgoVengers - Interactive CPU & Memory Management", 
                           bg=self.DARK_NAVY, fg=self.TEXT_LIGHT,
                           font=("Calibri", 10, "italic"))
        subtitle.pack()
        
        notebook = ttk.Notebook(self.root, style="TNotebook")
        self.cpu_tab = ttk.Frame(notebook, style="TFrame")
        self.mem_tab = ttk.Frame(notebook, style="TFrame")
        notebook.add(self.cpu_tab, text="🧠 CPU SCHEDULING")
        notebook.add(self.mem_tab, text="💾 MEMORY MANAGEMENT")
        notebook.pack(expand=1, fill="both", padx=15, pady=10)

        self.build_cpu_tab()
        self.build_mem_tab()

    def build_cpu_tab(self):
        frame = ttk.Frame(self.cpu_tab, padding=15, style="TFrame")
        frame.pack(expand=1, fill="both")

        # Process Input with animation
        input_fr = ttk.LabelFrame(frame, text="⚙️ Process Input", padding=12)
        input_fr.pack(fill="x", pady=10)
        
        instr_frame = tk.Frame(input_fr, bg=self.DARK_NAVY)
        instr_frame.pack(fill='x', pady=(0, 5))
        
        ttk.Label(instr_frame, text="📝 Enter one per line: PID Arrival Burst [Priority]  (e.g., P1 0 10 3)", 
                 font=("Calibri", 10)).pack(side='left')
        
        self.process_text = tk.Text(input_fr, height=6, bg=self.MID_BLUE, fg=self.TEXT_LIGHT, 
                                   insertbackground=self.ACCENT_BLUE, font=("Consolas", 11), 
                                   relief="solid", bd=2, borderwidth=2)
        self.process_text.pack(fill="x", pady=5)
        self.process_text.insert("1.0", "P1 0 8 3\nP2 1 4 1\nP3 2 9 4\nP4 3 5 2")
        
        # Add border highlight effect
        self.process_text.config(highlightbackground=self.ACCENT_BLUE, highlightthickness=1)

        # Algorithm Settings with standard buttons
        algo_fr = ttk.LabelFrame(frame, text="🎯 Algorithm Settings", padding=12)
        algo_fr.pack(fill="x", pady=10)
        
        settings_grid = tk.Frame(algo_fr, bg=self.DARK_NAVY)
        settings_grid.pack(fill="x")
        
        # Left side - Algorithm selection
        left_frame = tk.Frame(settings_grid, bg=self.DARK_NAVY)
        left_frame.pack(side='left', fill='both', expand=True)
        
        ttk.Label(left_frame, text="Select Algorithm:", font=("Calibri", 11)).grid(row=0, column=0, sticky="w", padx=5, pady=8)
        self.cpu_algo = ttk.Combobox(left_frame, values=["FCFS", "SJF", "Priority", "Round Robin"], 
                                     style="TCombobox", state="readonly", width=22, font=("Consolas", 11))
        self.cpu_algo.set("SJF")
        self.cpu_algo.grid(row=0, column=1, padx=10, pady=8, sticky="w")
        
        ttk.Label(left_frame, text="Time Quantum (for RR):", font=("Calibri", 11)).grid(row=1, column=0, sticky="w", padx=5, pady=8)
        self.quantum_entry = ttk.Entry(left_frame, style="TEntry", width=10, font=("Consolas", 11))
        self.quantum_entry.insert(0, "2")
        self.quantum_entry.grid(row=1, column=1, padx=10, pady=8, sticky="w")
        
        # Right side - Standard Run button
        right_frame = tk.Frame(settings_grid, bg=self.DARK_NAVY)
        right_frame.pack(side='right', padx=20)
        
        self.run_cpu_btn = tk.Button(right_frame, text="▶ RUN & COMPARE", 
                                     command=self.run_cpu_animated,
                                     bg=self.ACCENT_BLUE, fg=self.TEXT_DARK,
                                     font=("Calibri", 12, "bold"),
                                     width=18, height=2,
                                     relief="raised", bd=3,
                                     cursor="hand2",
                                     activebackground='#60B0FF',
                                     activeforeground=self.TEXT_DARK)
        self.run_cpu_btn.pack(pady=10)
        
        # Progress indicator
        self.cpu_progress = AnimatedProgress(algo_fr, width=500)
        self.cpu_progress.pack(pady=(10, 0))

        # Results & Gantt Chart
        result_fr = ttk.LabelFrame(frame, text="📊 Results Table", padding=12)
        result_fr.pack(fill="x", pady=10)

        columns = ("PID", "Arrival", "Burst", "Priority", "Waiting Time", "Turnaround Time")
        self.tree = ttk.Treeview(result_fr, columns=columns, show="headings", selectmode="none", height=6, style="Treeview")
        for col in columns:
            self.tree.heading(col, text=col)
            self.tree.column(col, anchor="center", width=int(1000/len(columns)))
        self.tree.pack(side="top", fill="x")

        self.summary_label = tk.Text(result_fr, height=12, bg=self.MID_BLUE, fg=self.TEXT_LIGHT, 
                                     insertbackground=self.ACCENT_BLUE, font=("Consolas", 11), 
                                     relief="solid", bd=2, wrap="none")
        self.summary_label.pack(fill="both", expand=True, pady=(8, 0))
        self.summary_label.config(highlightbackground=self.ACCENT_BLUE, highlightthickness=1)

        gantt_fr = ttk.LabelFrame(frame, text="📈 Gantt Chart Preview", padding=12)
        gantt_fr.pack(fill="both", expand=1, pady=10)
        
        info_label = tk.Label(gantt_fr, 
                             text="💡 A separate window will show *animated* comparative Gantt charts for all algorithms", 
                             bg=self.DARK_NAVY, fg='#FFD700', font=("Calibri", 10, "italic"),
                             wraplength=700)
        info_label.pack(pady=8)
        
        self.figure = plt.Figure(figsize=(9, 2.5), facecolor=self.DARK_NAVY)
        self.ax = self.figure.add_subplot(111)
        self.ax.set_facecolor(self.DARK_NAVY)
        self.ax.set_xticks([])
        self.ax.set_yticks([])
        self.canvas = FigureCanvasTkAgg(self.figure, master=gantt_fr)
        self.canvas.get_tk_widget().pack(fill="both", expand=1)

    def build_mem_tab(self):
        frame = ttk.Frame(self.mem_tab, padding=15, style="TFrame")
        frame.pack(expand=1, fill="both")

        # Memory Input with enhanced styling
        input_fr = ttk.LabelFrame(frame, text="💾 Page Replacement Input", padding=12)
        input_fr.pack(fill="x", pady=10)
        
        instr_frame = tk.Frame(input_fr, bg=self.DARK_NAVY)
        instr_frame.pack(fill='x', pady=(0, 5))
        
        ttk.Label(instr_frame, text="📝 Enter reference string (comma-separated): e.g., 7,0,1,2,0,3", 
                 font=("Calibri", 10)).pack(side='left')
        
        self.ref_entry = ttk.Entry(input_fr, style="TEntry", width=40, font=("Consolas", 11))
        self.ref_entry.insert(0, "7,0,1,2,0,3,0,4,2,3,0,3,2,1,2,0,1,7,0,1")
        self.ref_entry.pack(side='left', padx=(5, 5), pady=5)
        
        ttk.Label(input_fr, text="Frames:", font=("Calibri", 11)).pack(side='left', padx=(10, 0))
        self.frame_entry = ttk.Entry(input_fr, style="TEntry", width=5, font=("Consolas", 11))
        self.frame_entry.insert(0, "3")
        self.frame_entry.pack(side='left', padx=(0, 5), pady=5)

        # Algorithm Settings with standard buttons
        algo_fr = ttk.LabelFrame(frame, text="🎯 Algorithm Selection", padding=12)
        algo_fr.pack(fill="x", pady=10)
        
        settings_fr = tk.Frame(algo_fr, bg=self.DARK_NAVY)
        settings_fr.pack(fill="x")
        
        left_frame = tk.Frame(settings_fr, bg=self.DARK_NAVY)
        left_frame.pack(side='left', fill='both', expand=True)
        
        ttk.Label(left_frame, text="Select Algorithm:", font=("Calibri", 11)).pack(side='left', padx=5)
        self.mem_algo = ttk.Combobox(left_frame, values=["FIFO", "LRU", "Optimal"], 
                                     style="TCombobox", state="readonly", width=18, font=("Consolas", 11))
        self.mem_algo.set("LRU")
        self.mem_algo.pack(side='left', padx=10)
        
        right_frame = tk.Frame(settings_fr, bg=self.DARK_NAVY)
        right_frame.pack(side='right', padx=20)
        
        self.run_mem_btn = tk.Button(right_frame, text="▶ RUN SIMULATION (ANIMATED)", 
                                     command=self.run_memory_animated,
                                     bg='#FF6B6B', fg='#FFFFFF',
                                     font=("Calibri", 12, "bold"),
                                     width=25, height=2,
                                     relief="raised", bd=3,
                                     cursor="hand2",
                                     activebackground='#FF8787',
                                     activeforeground='#FFFFFF')
        self.run_mem_btn.pack()
        
        # Progress indicator
        self.mem_progress = AnimatedProgress(algo_fr, width=500)
        self.mem_progress.pack(pady=(10, 0))

        # Output with enhanced styling
        out_fr = ttk.LabelFrame(frame, text="📋 Memory Trace & Results", padding=12)
        out_fr.pack(fill="both", expand=1, pady=10)
        
        scrollbar = ttk.Scrollbar(out_fr)
        scrollbar.pack(side="right", fill="y")
        
        self.memory_output = tk.Text(out_fr, height=14, bg=self.MID_BLUE, fg=self.TEXT_LIGHT, 
                                     insertbackground=self.ACCENT_BLUE, font=("Consolas", 10), 
                                     relief="solid", bd=2, wrap="none", yscrollcommand=scrollbar.set)
        self.memory_output.pack(fill="both", expand=1)
        self.memory_output.config(highlightbackground=self.ACCENT_BLUE, highlightthickness=1)
        
        scrollbar.config(command=self.memory_output.yview)
    
    # --- Helper functions ---
    def compute_avg_metrics(self, procs):
        n = len(procs)
        total_wait = sum(p.get('waiting', 0) for p in procs)
        total_turn = sum(p.get('turnaround', 0) for p in procs)
        avg_wait = total_wait / n if n else 0
        avg_turn = total_turn / n if n else 0
        return avg_wait, avg_turn

    def run_cpu_animated(self):
        """Wrapper to show animation during CPU scheduling"""
        self.cpu_progress.start_animation()
        self.run_cpu_btn.config(state='disabled')
        # Schedule the heavy computation to run after a small delay
        self.root.after(500, self._execute_cpu)
    
    def _execute_cpu(self):
        try:
            self.run_cpu()
        finally:
            self.cpu_progress.stop_animation()
            self.run_cpu_btn.config(state='normal')

    def run_cpu(self):
        try:
            text = self.process_text.get("1.0", "end-1c").strip().splitlines()
            if not text:
                raise ValueError("Please enter processes.")
            
            base_processes = []
            for line in text:
                parts = line.split()
                if len(parts) < 3:
                    raise ValueError("Each line must have PID Arrival Burst [Priority].")
                pid, arr, burst = parts[0], int(parts[1]), int(parts[2])
                priority = int(parts[3]) if len(parts) > 3 else 1
                base_processes.append({'pid': pid, 'arrival': arr, 'burst': burst, 'orig_burst': burst, 'priority': priority})
                
            if not base_processes:
                 raise ValueError("No valid processes entered.")

            chosen_algo = self.cpu_algo.get()
            quantum = int(self.quantum_entry.get()) if self.quantum_entry.get().isdigit() and int(self.quantum_entry.get()) > 0 else 2

            # Execute all algorithms for comparison
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

            chosen_key = chosen_algo
            self.display_cpu_results(all_results[chosen_key]['gantt'], all_results[chosen_key]['procs'], chosen_key)
            self.show_comparative_gantt_animated(all_results, quantum)

        except Exception as e:
            messagebox.showerror("CPU Scheduling Error", str(e))

    def display_cpu_results(self, gantt, procs, algo):
        for item in self.tree.get_children():
            self.tree.delete(item)
            
        for p in procs:
            priority = p.get('priority', 1)
            self.tree.insert("", "end", values=(p['pid'], p['arrival'], p['burst'], priority, f"{p['waiting']:.2f}", f"{p['turnaround']:.2f}"))

        self.summary_label.delete(1.0, tk.END)
        avg_wait, avg_turn = self.compute_avg_metrics(procs)
        
        self.summary_label.insert(tk.END, f"✨ Detailed Metrics for: {algo}\n", 'title')
        self.summary_label.insert(tk.END, f"{'='*60}\n")
        self.summary_label.insert(tk.END, f"⏱️  Average Waiting Time: {avg_wait:.2f} units\n", 'metric')
        self.summary_label.insert(tk.END, f"⏲️  Average Turnaround Time: {avg_turn:.2f} units\n", 'metric')
        self.summary_label.insert(tk.END, f"🏁 Total Execution Time: {gantt[-1][2] if gantt else 0} units\n", 'metric')
        self.summary_label.insert(tk.END, f"📊 Number of Processes: {len(procs)}\n", 'metric')
        self.summary_label.insert(tk.END, f"{'='*60}\n")
        
        self.summary_label.tag_config('title', foreground='#41A0FF', font=('Consolas', 11, 'bold'))
        self.summary_label.tag_config('metric', foreground='#E0FBFC', font=('Consolas', 10))

    def show_comparative_gantt_animated(self, all_results, quantum):
        """Show animated comparative Gantt chart in popup"""
        algos = ["FCFS", "SJF", "Priority", "Round Robin"]
        
        unique_pids = sorted(list(set(pid for res in all_results.values() for pid, s, e in res['gantt'])))

        cmap = cm.get_cmap('tab20')
        pid_colors = {pid: cmap(i % 20) for i, pid in enumerate(unique_pids)}

        max_time = 0
        for res in all_results.values():
            for pid, s, e in res['gantt']:
                if e > max_time:
                    max_time = e

        if max_time == 0:
            max_time = 1

        win = tk.Toplevel(self.root)
        win.title("🎬 Animated Comparative Gantt Charts")
        win.configure(bg=self.DARK_NAVY)
        win.geometry("1050x750")

        # Header
        header = tk.Frame(win, bg=self.DARK_NAVY, height=50)
        header.pack(fill='x', pady=10)
        tk.Label(header, text="📊 Algorithm Comparison - Gantt Charts", 
                bg=self.DARK_NAVY, fg=self.ACCENT_BLUE,
                font=("Calibri", 18, "bold")).pack()

        fig, axs = plt.subplots(len(algos), 1, figsize=(10, 2.3 * len(algos)), 
                               sharex=True, facecolor=self.DARK_NAVY)
        if len(algos) == 1:
            axs = [axs]

        # Initialize empty charts
        for ax, algo in zip(axs, algos):
            ax.set_facecolor(self.DARK_NAVY)
            ax.set_ylabel(algo, color=self.TEXT_LIGHT, fontsize=11, fontweight='bold')
            ax.tick_params(axis='y', colors=self.TEXT_LIGHT)
            ax.tick_params(axis='x', colors=self.TEXT_LIGHT)
            ax.set_yticks([])
            ax.set_xlim(0, max_time)
            ax.set_xticks(list(range(0, max_time + 1, max(1, max_time // 10)))) # Dynamic ticks
            ax.set_xlabel('Time (units)', color=self.TEXT_LIGHT, fontsize=10)
            ax.grid(True, alpha=0.2, color=self.TEXT_LIGHT)

        plt.tight_layout()

        canvas = FigureCanvasTkAgg(fig, master=win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill='both', expand=True, padx=10, pady=5)

        # Legend
        legend_frame = tk.Frame(win, bg=self.DARK_NAVY, height=50)
        legend_frame.pack(fill='x', pady=10)
        
        tk.Label(legend_frame, text="Process Legend: ", 
                bg=self.DARK_NAVY, fg=self.TEXT_LIGHT, 
                font=("Calibri", 10, "bold")).pack(side='left', padx=10)
        
        for pid in unique_pids:
            c = pid_colors[pid]
            hex_color = matplotlib.colors.to_hex(c)
            sw = tk.Canvas(legend_frame, width=20, height=16, bg=self.DARK_NAVY, highlightthickness=0)
            sw.create_rectangle(0, 0, 20, 16, fill=hex_color, outline='#ffffff', width=1)
            lbl = tk.Label(legend_frame, text=f" {pid} ", bg=self.DARK_NAVY, fg=self.TEXT_LIGHT, font=("Consolas", 9, "bold"))
            sw.pack(side='left', padx=(8, 2))
            lbl.pack(side='left', padx=(0, 8))
            
        # Metrics comparison frame (hidden initially)
        self.metrics_frame = tk.Frame(win, bg=self.MID_BLUE, relief='solid', bd=2)
        
        # Animation state
        animation_data = {'current_time': 0, 'completed': False, 'interval_ms': 100}

        def animate_gantt():
            if animation_data['completed']:
                return
            
            t = animation_data['current_time']
            
            for ax, algo in zip(axs, algos):
                ax.clear()
                ax.set_facecolor(self.DARK_NAVY)
                ax.set_ylabel(algo, color=self.TEXT_LIGHT, fontsize=11, fontweight='bold')
                ax.tick_params(axis='y', colors=self.TEXT_LIGHT)
                ax.tick_params(axis='x', colors=self.TEXT_LIGHT)
                ax.set_yticks([])
                ax.set_xlim(0, max_time)
                ax.set_xticks(list(range(0, max_time + 1, max(1, max_time // 10))))
                ax.set_xlabel('Time (units)', color=self.TEXT_LIGHT, fontsize=10)
                ax.grid(True, alpha=0.2, color=self.TEXT_LIGHT)
                
                gantt = all_results.get(algo, {}).get('gantt', [])
                for pid, start, end in gantt:
                    if start < t:
                        visible_end = min(end, t)
                        duration = visible_end - start
                        ax.broken_barh([(start, duration)], (0, 5), 
                                      facecolors=[pid_colors.get(pid, (0.6, 0.6, 0.6))],
                                      edgecolors='white', linewidth=1.5)
                        
                        # Add PID label when execution finishes or is running for a while
                        if duration > 0 and (visible_end == end or duration > 1.5):
                            ax.text(start + duration / 2, 2.5, pid, 
                                   ha='center', va='center', 
                                   color='black' if sum(pid_colors.get(pid, (0.6,0.6,0.6))[:3]) > 1.5 else 'white', 
                                   fontsize=9, fontweight='bold')
                            
                # Draw the current time marker
                ax.axvline(x=t, color='red', linestyle='--', linewidth=1.5)

            canvas.draw()
            
            animation_data['current_time'] += 0.5
            if animation_data['current_time'] > max_time + 1:
                animation_data['completed'] = True
                
                # Show final metrics comparison
                self.metrics_frame.pack(fill='x', padx=20, pady=10)
                
                # Clear previous content
                for widget in self.metrics_frame.winfo_children():
                    widget.destroy()

                tk.Label(self.metrics_frame, text="⚡ Performance Comparison", 
                        bg=self.MID_BLUE, fg='#FFD700', 
                        font=("Calibri", 12, "bold")).pack(pady=5)
                
                for algo in algos:
                    avg_wait, avg_turn = all_results[algo]['avg']
                    metric_text = f"[{algo.ljust(12)}]: Avg Wait={avg_wait:.2f}, Avg Turnaround={avg_turn:.2f}"
                    tk.Label(self.metrics_frame, text=metric_text, 
                            bg=self.MID_BLUE, fg=self.TEXT_LIGHT,
                            font=("Consolas", 10)).pack(anchor='w', padx=20, pady=2)
                
                return
            
            win.after(animation_data['interval_ms'], animate_gantt)

        def on_close():
            animation_data['completed'] = True
            plt.close(fig)
            win.destroy()
        
        win.protocol("WM_DELETE_WINDOW", on_close)
        
        # Start animation after window is visible
        win.after(300, animate_gantt)

    def run_memory_animated(self):
        """Wrapper to show animation during memory simulation"""
        # Ensure any previous animator is stopped
        if self.animator:
            self.animator.stop_animation()
            self.animator = None
            
        self.mem_progress.start_animation()
        self.run_mem_btn.config(state='disabled')
        self.root.after(500, self._execute_memory)
    
    def _execute_memory(self):
        try:
            self.run_memory()
        except Exception as e:
            if self.animator:
                self.animator.stop_animation()
            messagebox.showerror("Memory Simulation Error", str(e))
        finally:
            self.mem_progress.stop_animation()
            self.run_mem_btn.config(state='normal')

    def run_memory(self):
        try:
            ref_str = self.ref_entry.get().strip()
            if not ref_str:
                raise ValueError("Please enter a reference string.")
            pages = [int(x.strip()) for x in ref_str.split(',') if x.strip() !=""]

            frames = int(self.frame_entry.get()) if self.frame_entry.get().isdigit() and int(self.frame_entry.get()) > 0 else 3
            if frames <= 0:
                 raise ValueError("Number of frames must be positive.")
                 
            algo = self.mem_algo.get()

            # Execute the algorithm to get the full trace history
            if algo == 'FIFO':
                faults, history = fifo_page_replacement(pages, frames)
            elif algo == 'LRU':
                faults, history = lru_page_replacement(pages, frames)
            else:
                faults, history = optimal_page_replacement(pages, frames)

            # Start the animated trace instead of static output
            self.animator = self.MemoryTraceAnimator(self.memory_output, history, pages, frames, algo, self.root)
            self.animator.start_animation()
            
        except Exception as e:
            # Re-raise the exception to be caught by _execute_memory
            raise e


if __name__ == '__main__':
    root = tk.Tk()
    app = OSSimulator(root)
    root.mainloop()