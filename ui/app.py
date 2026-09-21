"""
SATPLAN Problem Browser — Streamlit UI

Run: streamlit run ui/app.py  (from the repo root)
"""

from __future__ import annotations
import base64
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

import streamlit as st

REPO_ROOT = Path(__file__).resolve().parent.parent
BB_DIR    = REPO_ROOT / "Blackbox" / "blackbox_python"

PLANNERS = {
    "SATplan":  str(REPO_ROOT / "satplan_python" / "satplan.py"),
    "BlackBox": str(BB_DIR / "blackbox.py"),
    "STRIPS":   str(REPO_ROOT / "strips_python" / "strips.py"),
}

# Planners that take a "-solver <name>" SAT-solver spec. STRIPS is plain
# forward state-space search (AIMA-style) and has no SAT solver to choose.
SAT_PLANNERS = {"SATplan", "BlackBox"}

ANIMATORS = {
    "Blocksworld": str(BB_DIR / "animate_blocksworld.py"),
    "Ferry":       str(BB_DIR / "animate_ferry.py"),
    "Hanoi":       str(BB_DIR / "animate_hanoi.py"),
    "Elevator":    str(BB_DIR / "animate_elevator.py"),
}

DOMAIN_FILES = {
    "Blocksworld": str(REPO_ROOT / "benchmarks" / "blocks_domain.pddl"),
    "Ferry":       str(REPO_ROOT / "benchmarks" / "ferry_domain.pddl"),
    "Hanoi":       str(REPO_ROOT / "benchmarks" / "hanoi_domain.pddl"),
    "Elevator":    str(BB_DIR / "pddl_problems" / "elevator_domain.pddl"),
}

# "Custom" is a domain option like the others, but has no generator, no
# fixed domain file, and no animator — the user supplies both PDDL files.
ALL_DOMAINS = ["Blocksworld", "Elevator", "Ferry", "Hanoi", "Custom"]

# Anim horizon cap per domain (can go large since we use satplan)
ANIM_STEPS = {"Blocksworld": 20, "Ferry": 40, "Hanoi": 40, "Elevator": 30}

SAT_SOLVERS = {
    "CaDiCaL (default)": "cadical",
    "Glucose":           "glucose",
    "MapleChrono":       "maple",
    "MiniSat":           "minisat",
    "Kissat":            "kissat",
    "WalkSAT":           "walksat",
}


def _init_state() -> None:
    defaults: dict = {
        "domain":           ALL_DOMAINS[0],
        "last_output":      "",
        "last_problem":     "",
        "last_anim_gif":    "",
        "last_anim_key":    "",
        "pddl_text_key":    "",
        "pddl_default":     "",
        "pddl_version":     0,
        "custom_output":    "",
        "custom_domain_text":  "",
        "custom_problem_text": "",
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v


def _parse_output(text: str) -> dict:
    import re
    plan_len   = re.search(r"(\d+) actions in plan", text)
    total_time = re.search(r"Total time:\s*([\d.]+)", text)
    horizon    = re.findall(r"Trying (?:horizon|plan length) (\d+)", text)
    return {
        "plan_len":    plan_len.group(1) if plan_len else None,
        "total_time":  total_time.group(1) + "s" if total_time else None,
        "max_horizon": horizon[-1] if horizon else None,
    }


def _gif_path(key: str) -> str:
    safe = key.replace(" ", "_").replace("/", "_")
    return str(Path(tempfile.gettempdir()) / f"satplan_anim_{safe}.gif")


def _domain_params(domain: str) -> dict:
    """Render domain-specific sliders and return the current params dict."""
    if domain == "Blocksworld":
        n = st.slider("Number of blocks", min_value=2, max_value=10, value=3, step=1)
        return {"blocks": n}
    if domain == "Ferry":
        n = st.slider("Number of cars", min_value=1, max_value=12, value=4, step=1)
        return {"cars": n}
    if domain == "Hanoi":
        n = st.slider("Number of discs", min_value=2, max_value=6, value=3, step=1)
        return {"discs": n}
    if domain == "Elevator":
        c1, c2, c3 = st.columns(3)
        with c1:
            p = st.slider("Passengers", min_value=1, max_value=15, value=2, step=1)
        with c2:
            e = st.slider("Elevators", min_value=1, max_value=3, value=1, step=1)
        with c3:
            f = st.slider("Floors", min_value=2, max_value=10, value=4, step=1)
        return {"passengers": p, "elevators": e, "floors": f}
    return {}


def _generate_pddl_text(domain: str, params: dict) -> str:
    """Generate PDDL problem text for the current sliders (no file I/O)."""
    sys.path.insert(0, str(REPO_ROOT / "ui"))
    from pddl_generator import (gen_blocksworld_pddl, gen_ferry_pddl,
                                 gen_hanoi_pddl, gen_elevator_pddl)

    if domain == "Blocksworld":
        return gen_blocksworld_pddl(params["blocks"])
    if domain == "Ferry":
        return gen_ferry_pddl(params["cars"])
    if domain == "Hanoi":
        return gen_hanoi_pddl(params["discs"])
    return gen_elevator_pddl(params["passengers"], params["elevators"], params["floors"])


def _write_text(path: Path, text: str) -> str:
    path.write_text(text)
    return str(path)


def _param_key(domain: str, params: dict) -> str:
    parts = [domain] + [f"{k}{v}" for k, v in sorted(params.items())]
    return "_".join(parts)


def _content_key(domain: str, text: str) -> str:
    """Cache key derived from the actual PDDL text, so hand-edited problems
    (e.g. a custom multi-stack blocksworld state) get their own cache slot
    instead of reusing a stale slider-generated one."""
    h = hashlib.md5(text.encode()).hexdigest()[:10]
    return f"{domain}_{h}"


def _build_solver_cmd(planner_name: str, domain_path: str, problem_path: str,
                      solver_name: str | None) -> list[str]:
    cmd = [sys.executable, PLANNERS[planner_name], "-o", domain_path, "-f", problem_path]
    if planner_name == "SATplan":
        cmd += ["-noopt"]
    if planner_name in SAT_PLANNERS and solver_name:
        cmd += ["-solver", solver_name]
    return cmd


def main() -> None:
    st.set_page_config(page_title="SATPLAN Browser", layout="centered")
    st.title("SATPLAN Problem Browser")
    _init_state()

    # ── Domain + planner + solver selectors ───────────────────────────────
    col_domain, col_planner, col_solver = st.columns(3)
    with col_domain:
        new_domain = st.selectbox("Domain", ALL_DOMAINS,
                                  index=ALL_DOMAINS.index(st.session_state.domain))
    with col_planner:
        planner_name = st.selectbox("Planner", list(PLANNERS.keys()))
    with col_solver:
        if planner_name in SAT_PLANNERS:
            solver_label = st.selectbox("SAT Solver", list(SAT_SOLVERS.keys()))
            solver_name  = SAT_SOLVERS[solver_label]
        else:
            st.selectbox("SAT Solver", ["N/A — forward search"], disabled=True)
            solver_name = None

    if new_domain != st.session_state.domain:
        st.session_state.domain        = new_domain
        st.session_state.last_output   = ""
        st.session_state.last_anim_gif = ""
        st.session_state.last_anim_key = ""

    domain = st.session_state.domain
    st.divider()

    if domain == "Custom":
        _run_custom_domain(planner_name, solver_name)
    else:
        _run_builtin_domain(domain, planner_name, solver_name)


def _run_builtin_domain(domain: str, planner_name: str, solver_name: str | None) -> None:
    # BlackBox is the GraphPlan-based planner, so its animation shows the
    # planning-graph panel; SATplan/STRIPS have no graph to show.
    show_graph = planner_name == "BlackBox"
    params    = _domain_params(domain)
    param_key = _param_key(domain, params)

    sys.path.insert(0, str(REPO_ROOT / "ui"))
    from pddl_generator import describe
    st.caption(describe(domain, params))

    domain_path = DOMAIN_FILES[domain]

    # Regenerate the default PDDL whenever the domain/sliders change,
    # discarding any hand edits made for the previous configuration.
    if st.session_state.pddl_text_key != param_key:
        st.session_state.pddl_text_key = param_key
        st.session_state.pddl_default  = _generate_pddl_text(domain, params)
        st.session_state.pddl_version += 1

    with st.expander("Problem PDDL (editable)", expanded=False):
        st.caption(
            "Edit freely — split blocks into multiple stacks, reorder them, "
            "or change the goal. The solver and animation below use exactly "
            "what's in this box."
        )
        widget_key = f"pddl_editor_{st.session_state.pddl_version}"
        pddl_text = st.text_area(
            "Problem PDDL",
            value=st.session_state.get(widget_key, st.session_state.pddl_default),
            height=280,
            key=widget_key,
            label_visibility="collapsed",
        )
        if st.button("Reset to generated"):
            st.session_state.pddl_default = _generate_pddl_text(domain, params)
            st.session_state.pddl_version += 1
            st.rerun()

    content_key = _content_key(domain, pddl_text)

    # ── Run solver ────────────────────────────────────────────────────────
    st.divider()
    run_col, timeout_col = st.columns([3, 1])
    with timeout_col:
        timeout_secs = st.number_input("Timeout (s)", min_value=5, max_value=300,
                                       value=60, step=5)
    with run_col:
        run_pressed = st.button("Run Solver", type="primary", use_container_width=True)

    if run_pressed:
        problem_path = _write_text(
            Path(tempfile.gettempdir()) / f"satplan_prob_{domain.lower()}.pddl", pddl_text)
        cmd = _build_solver_cmd(planner_name, domain_path, problem_path, solver_name)
        try:
            with st.spinner("Solving..."):
                result = subprocess.run(
                    cmd, capture_output=True, text=True,
                    timeout=timeout_secs, cwd=str(REPO_ROOT),
                )
            st.session_state.last_output = result.stdout + (
                ("\n--- stderr ---\n" + result.stderr) if result.stderr.strip() else ""
            )
        except subprocess.TimeoutExpired:
            st.session_state.last_output = f"[TIMEOUT after {timeout_secs}s]"
        st.session_state.last_problem = content_key
        st.rerun()

    if st.session_state.last_output:
        parsed = _parse_output(st.session_state.last_output)
        m1, m2, m3 = st.columns(3)
        m1.metric("Plan length",       parsed["plan_len"]    or "—")
        m2.metric("Total time",        parsed["total_time"]  or "—")
        m3.metric("Max horizon tried", parsed["max_horizon"] or "—")
        st.code(st.session_state.last_output, language="text")

    # ── Animation ─────────────────────────────────────────────────────────
    st.divider()
    animator = ANIMATORS.get(domain)

    SPEED_OPTIONS = {"Slow": 2000, "Normal": 800, "Fast": 400, "Very Fast": 200}
    anim_col, speed_col, anim_timeout_col = st.columns([2, 1, 1])
    with speed_col:
        speed_label = st.selectbox("Speed", list(SPEED_OPTIONS.keys()), index=1)
        anim_interval = SPEED_OPTIONS[speed_label]
    with anim_timeout_col:
        anim_timeout = st.number_input("Anim timeout (s)", min_value=30,
                                       max_value=600, value=240, step=30)

    anim_key   = f"{content_key}_spd{anim_interval}_{'graph' if show_graph else 'nograph'}"
    gif_out    = _gif_path(anim_key)
    gif_exists = (
        st.session_state.last_anim_key == anim_key
        and st.session_state.last_anim_gif == gif_out
        and Path(gif_out).exists()
    )

    with anim_col:
        anim_pressed = st.button(
            "Regenerate Animation" if gif_exists else "Generate Animation",
            use_container_width=True,
            type="primary",
        )

    if anim_pressed:
        problem_path = _write_text(
            Path(tempfile.gettempdir()) / f"satplan_prob_{domain.lower()}.pddl", pddl_text)
        steps = ANIM_STEPS.get(domain, 25)
        cmd = [
            sys.executable, animator,
            "-o", domain_path,
            "-f", problem_path,
            "--save", gif_out,
            "--steps", str(steps),
            "--no-noop",
            "--interval", str(anim_interval),
        ]
        if not show_graph:
            cmd.append("--no-graph")
        try:
            with st.spinner(
                f"Rendering animation (up to {steps} horizons) — "
                "this may take a minute for larger problems…"
            ):
                result = subprocess.run(
                    cmd, capture_output=True, text=True,
                    timeout=anim_timeout, cwd=str(REPO_ROOT),
                )
            if result.returncode != 0:
                st.error("Animation failed:\n" + result.stderr)
                st.session_state.last_anim_gif = ""
            else:
                st.session_state.last_anim_gif = gif_out
                st.session_state.last_anim_key = anim_key
                st.rerun()
        except subprocess.TimeoutExpired:
            st.error(f"Animation timed out after {anim_timeout}s.")
            st.session_state.last_anim_gif = ""

    if st.session_state.last_anim_gif and Path(st.session_state.last_anim_gif).exists():
        gif_bytes = Path(st.session_state.last_anim_gif).read_bytes()
        b64 = base64.b64encode(gif_bytes).decode()
        st.markdown(
            f'<img src="data:image/gif;base64,{b64}" '
            f'style="width:100%;border-radius:6px;" />',
            unsafe_allow_html=True,
        )
        st.caption(f"Plan execution — {describe(domain, params)}")


def _run_custom_domain(planner_name: str, solver_name: str | None) -> None:
    st.caption(
        "Provide your own domain and problem PDDL — paste text directly or "
        "upload files. No animation is shown here; custom domains aren't "
        "tied to one of the built-in renderers."
    )

    input_mode = st.radio("Input method", ["Paste text", "Upload files"],
                          horizontal=True, key="custom_input_mode")

    domain_text  = st.session_state.custom_domain_text
    problem_text = st.session_state.custom_problem_text

    if input_mode == "Paste text":
        c1, c2 = st.columns(2)
        with c1:
            domain_text = st.text_area(
                "Domain PDDL", height=260, key="custom_domain_text",
                placeholder="(define (domain my-domain)\n"
                           "  (:requirements :strips)\n"
                           "  (:predicates ...)\n"
                           "  (:action ...))",
            )
        with c2:
            problem_text = st.text_area(
                "Problem PDDL", height=260, key="custom_problem_text",
                placeholder="(define (problem my-problem)\n"
                           "  (:domain my-domain)\n"
                           "  (:objects ...)\n"
                           "  (:init ...)\n"
                           "  (:goal (and ...)))",
            )
    else:
        c1, c2 = st.columns(2)
        with c1:
            domain_file = st.file_uploader("Domain PDDL file", type=["pddl", "txt"],
                                           key="custom_domain_file")
            if domain_file:
                domain_text = domain_file.getvalue().decode()
                st.session_state.custom_domain_text = domain_text
        with c2:
            problem_file = st.file_uploader("Problem PDDL file", type=["pddl", "txt"],
                                            key="custom_problem_file")
            if problem_file:
                problem_text = problem_file.getvalue().decode()
                st.session_state.custom_problem_text = problem_text
        if domain_text:
            with st.expander("Domain PDDL (loaded)"):
                st.code(domain_text, language="lisp")
        if problem_text:
            with st.expander("Problem PDDL (loaded)"):
                st.code(problem_text, language="lisp")

    st.divider()
    run_col, timeout_col = st.columns([3, 1])
    with timeout_col:
        timeout_secs = st.number_input("Timeout (s)", min_value=5, max_value=300,
                                       value=60, step=5, key="custom_timeout")
    with run_col:
        run_pressed = st.button(
            "Run Solver", type="primary", use_container_width=True,
            disabled=not (domain_text.strip() and problem_text.strip()),
        )

    if run_pressed:
        domain_path  = _write_text(
            Path(tempfile.gettempdir()) / "satplan_custom_domain.pddl", domain_text)
        problem_path = _write_text(
            Path(tempfile.gettempdir()) / "satplan_custom_problem.pddl", problem_text)
        cmd = _build_solver_cmd(planner_name, domain_path, problem_path, solver_name)
        try:
            with st.spinner("Solving..."):
                result = subprocess.run(
                    cmd, capture_output=True, text=True,
                    timeout=timeout_secs, cwd=str(REPO_ROOT),
                )
            st.session_state.custom_output = result.stdout + (
                ("\n--- stderr ---\n" + result.stderr) if result.stderr.strip() else ""
            )
        except subprocess.TimeoutExpired:
            st.session_state.custom_output = f"[TIMEOUT after {timeout_secs}s]"
        st.rerun()

    if st.session_state.custom_output:
        parsed = _parse_output(st.session_state.custom_output)
        m1, m2, m3 = st.columns(3)
        m1.metric("Plan length",       parsed["plan_len"]    or "—")
        m2.metric("Total time",        parsed["total_time"]  or "—")
        m3.metric("Max horizon tried", parsed["max_horizon"] or "—")
        st.code(st.session_state.custom_output, language="text")


if __name__ == "__main__":
    main()
