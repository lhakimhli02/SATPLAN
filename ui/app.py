"""
SATPLAN Problem Browser — Streamlit UI

Run: streamlit run ui/app.py  (from the repo root)
"""

from __future__ import annotations
import base64
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
}

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

ALL_DOMAINS = ["Blocksworld", "Elevator", "Ferry", "Hanoi"]

# Anim horizon cap per domain (can go large since we use satplan)
ANIM_STEPS = {"Blocksworld": 20, "Ferry": 40, "Hanoi": 40, "Elevator": 30}


def _init_state() -> None:
    defaults: dict = {
        "domain":           ALL_DOMAINS[0],
        "last_output":      "",
        "last_problem":     "",
        "last_anim_gif":    "",
        "last_anim_key":    "",
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


def _write_problem(domain: str, params: dict) -> str:
    """Generate PDDL for current params, write to a temp file, return path."""
    import sys, os
    sys.path.insert(0, str(REPO_ROOT / "ui"))
    from pddl_generator import (gen_blocksworld_pddl, gen_ferry_pddl,
                                 gen_hanoi_pddl, gen_elevator_pddl)

    if domain == "Blocksworld":
        pddl = gen_blocksworld_pddl(params["blocks"])
    elif domain == "Ferry":
        pddl = gen_ferry_pddl(params["cars"])
    elif domain == "Hanoi":
        pddl = gen_hanoi_pddl(params["discs"])
    else:
        pddl = gen_elevator_pddl(params["passengers"], params["elevators"], params["floors"])

    tmp = Path(tempfile.gettempdir()) / f"satplan_prob_{domain.lower()}.pddl"
    tmp.write_text(pddl)
    return str(tmp)


def _param_key(domain: str, params: dict) -> str:
    parts = [domain] + [f"{k}{v}" for k, v in sorted(params.items())]
    return "_".join(parts)


def main() -> None:
    st.set_page_config(page_title="SATPLAN Browser", layout="centered")
    st.title("SATPLAN Problem Browser")
    _init_state()

    SAT_SOLVERS = {
        "CaDiCaL (default)": "cadical",
        "Glucose":           "glucose",
        "MapleChrono":       "maple",
        "MiniSat":           "minisat",
        "Kissat":            "kissat",
        "WalkSAT":           "walksat",
    }

    # ── Domain + planner + solver selectors ───────────────────────────────
    col_domain, col_planner, col_solver = st.columns(3)
    with col_domain:
        new_domain = st.selectbox("Domain", ALL_DOMAINS,
                                  index=ALL_DOMAINS.index(st.session_state.domain))
    with col_planner:
        planner_name = st.selectbox("Planner", list(PLANNERS.keys()))
    with col_solver:
        solver_label = st.selectbox("SAT Solver", list(SAT_SOLVERS.keys()))
        solver_name  = SAT_SOLVERS[solver_label]

    if new_domain != st.session_state.domain:
        st.session_state.domain      = new_domain
        st.session_state.last_output = ""
        st.session_state.last_anim_gif = ""
        st.session_state.last_anim_key = ""

    domain = st.session_state.domain

    # ── Problem parameters ────────────────────────────────────────────────
    st.divider()
    params = _domain_params(domain)

    sys.path.insert(0, str(REPO_ROOT / "ui"))
    from pddl_generator import describe
    st.caption(describe(domain, params))

    param_key    = _param_key(domain, params)
    domain_path  = DOMAIN_FILES[domain]

    # Show generated PDDL
    with st.expander("Problem PDDL"):
        problem_path = _write_problem(domain, params)
        st.code(Path(problem_path).read_text(), language="lisp")

    # ── Run solver ────────────────────────────────────────────────────────
    st.divider()
    run_col, timeout_col = st.columns([3, 1])
    with timeout_col:
        timeout_secs = st.number_input("Timeout (s)", min_value=5, max_value=300,
                                       value=60, step=5)
    with run_col:
        run_pressed = st.button("Run Solver", type="primary", use_container_width=True)

    if run_pressed:
        problem_path = _write_problem(domain, params)
        cmd = [sys.executable, PLANNERS[planner_name], "-o", domain_path, "-f", problem_path,
               "-solver", solver_name]
        if planner_name == "SATplan":
            cmd += ["-noopt"]
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
        st.session_state.last_problem = param_key
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

    anim_key   = f"{param_key}_spd{anim_interval}"
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
        problem_path = _write_problem(domain, params)
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
        st.caption(
            f"GraphPlan search + plan execution — {describe(domain, params)}"
        )


if __name__ == "__main__":
    main()
