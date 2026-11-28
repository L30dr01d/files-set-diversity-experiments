"""Interactive figures assembled from the planned cells and their checkpoints."""

from collections import defaultdict
from pathlib import Path

import plotly.graph_objects as go
from plotly.subplots import make_subplots

from .coverage_with_filter import COLUMNS, PLOT_ROWS
from .results import collect_cells
from .score_for_fastr import BUDGET_PCTS
from .score_for_panhard import PANHARD


def build_figure(exp, cells):
    panels = defaultdict(list)
    stops = {}
    shared = {}
    missing = partial = 0
    for (dataset, column), payload in cells.items():
        data = payload or {}
        missing += int(payload is None or ("value" in data and data["value"] is None))
        if exp.type in ("score_per_measure", "measure_per_set"):
            by_tool = exp.type == "score_per_measure"
            title, category = (column, dataset) if by_tool else (dataset, column)
            trace = go.Scatter(mode="markers") if by_tool else go.Bar()
            trace.update(
                x=[category],
                y=[data.get("value")],
                name=category,
                customdata=[[data.get("seconds"), data.get("peak_memory_mib")]],
                hovertemplate="%{x}<br>Score %{y}<br>Seconds %{customdata[0]}<br>MiB %{customdata[1]}<extra></extra>",
            )
            panels[title, "Score", 1].append(trace)
        elif exp.type == "score_for_fastr":
            failed = [
                entry["measures"][tool]["value"] is None
                for entry in data.values()
                for tool in exp.scorers
            ]
            if failed:
                missing += int(all(failed))
                partial += int(any(failed) and not all(failed))
            for scorer in exp.scorers:
                ys = [
                    (data.get(str(p), {}).get("measures", {}).get(scorer) or {}).get(
                        "value"
                    )
                    for p in BUDGET_PCTS
                ]
                panels[f"{dataset} · {column}", "Score", 1].append(
                    go.Scatter(
                        x=[f"{p}%" for p in BUDGET_PCTS],
                        y=ys,
                        name=scorer,
                        mode="lines+markers",
                    )
                )
        elif exp.type == "coverage_with_filter":
            for analyzer, label, _ in PLOT_ROWS:
                for metric, title, adequate in COLUMNS:
                    if analyzer == "both" and not adequate:
                        continue
                    unit = "Files kept (%)" if adequate else "Coverage (%)"
                    panel = panels[f"{dataset} · {label} · {title}", unit, 100]
                    if adequate:
                        counts = (
                            data.get("adequacy", {}).get(analyzer, {}).get(metric, [])
                        )
                        panel.append(
                            go.Box(
                                y=[
                                    100 * n / data["dataset_size"]
                                    for n in counts
                                    if data["dataset_size"]
                                ],
                                name=label,
                            )
                        )
                    else:
                        for budget, draws in (
                            data.get("budgets", {}).get(analyzer, {}).items()
                        ):
                            panel.append(
                                go.Box(
                                    y=[draw[metric] for draw in draws],
                                    name=f"{budget}%",
                                )
                            )
        elif exp.type.startswith("coverage_"):
            steps = data.get("steps") or []
            missing += int(payload is not None and not steps)
            x = [s["remaining_count"] for s in steps]
            key = (dataset, "Panhard diversity", 1)
            panels[key].append(
                go.Scatter(
                    x=x,
                    y=[s["score"] for s in steps],
                    error_y=dict(array=[abs(s["residual"]) for s in steps]),
                    name="Panhard",
                )
            )
            stops[key] = data.get("stop_count")
            for metric in ("line", "mcdc"):
                key = (dataset, f"{metric.upper()} coverage (%)", 100)
                stops[key] = data.get("stop_count")
                for analyzer, label, _ in PLOT_ROWS:
                    if analyzer != "both":
                        panels[key].append(
                            go.Bar(
                                x=x,
                                y=[s["coverage"][analyzer][metric] for s in steps],
                                name=label,
                            )
                        )
        else:
            random = exp.type == "score_for_random_filter"
            base = (exp.filter_tool or exp.tools[0]) if random else PANHARD
            key = (dataset, "Score", 1)
            panel = panels[key]
            groups = defaultdict(lambda: defaultdict(list))
            runs = data.get("runs", []) if random else [data]
            if payload:
                failed = [
                    not run.get("steps") or step["measures"][column]["value"] is None
                    for run in runs
                    for step in (run.get("steps") or [None])
                ]
                missing += int(not failed or all(failed))
                partial += int(bool(failed) and any(failed) and not all(failed))
            for run in runs:
                steps = run.get("steps") or []
                if not steps:
                    continue
                seed = run.get("seed")
                identity = (dataset, seed)
                signature = (
                    data.get("stop_count"),
                    [
                        (
                            s["remaining_count"],
                            s.get("subset_digest"),
                            s["measures"][base]["value"],
                            s["measures"][base].get("residual"),
                        )
                        for s in steps
                    ],
                )
                repeated = identity in shared
                if repeated and shared[identity] != signature:
                    raise ValueError(f"inconsistent shared trace {identity}")
                shared[identity] = signature
                tools = tuple(dict.fromkeys((base, column)))
                for tool in tools:
                    if tool == base and repeated:
                        continue
                    if random:
                        seen_counts = set()
                        for step in steps:
                            count = step["remaining_count"]
                            if count not in seen_counts:
                                groups[tool][count, step["remaining_pct"]].append(
                                    step["measures"][tool]["value"]
                                )
                                seen_counts.add(count)
                    else:
                        measures = [s["measures"][tool] for s in steps]
                        residual = (
                            [abs(m["residual"]) for m in measures]
                            if tool == PANHARD
                            else None
                        )
                        panel.append(
                            go.Scatter(
                                x=[s["remaining_count"] for s in steps],
                                y=[m["value"] for m in measures],
                                name=tool,
                                error_y=dict(array=residual) if residual else None,
                            )
                        )
                if not random:
                    stops[key] = data["stop_count"]
            for tool, counts in groups.items():
                xs, ys = [], []
                for (count, pct), scores in sorted(counts.items(), reverse=True):
                    xs.extend([f"{pct:.1f}% · {count} · n={len(scores)}"] * len(scores))
                    ys.extend(scores)
                panel.append(go.Box(x=xs, y=ys, name=tool))

    return _layout(exp, panels, stops, missing, partial)


def _layout(exp, panels, stops, missing, partial):
    fig = make_subplots(
        rows=len(panels),
        cols=1,
        subplot_titles=[p[0] for p in panels],
        vertical_spacing=min(0.08, 0.4 / len(panels)),
    )
    fit, full = {}, {}
    for row, (key, traces) in enumerate(panels.items(), 1):
        _, unit, upper = key
        for trace in traces:
            fig.add_trace(trace, row=row, col=1)
        fig.update_yaxes(title_text=unit, row=row, col=1)
        if exp.type == "score_for_fastr":
            xlabel = "Budget (% of original suite)"
        elif exp.type == "score_for_random_filter":
            xlabel = "Remaining files (% · count · sample size)"
        elif exp.type.startswith(("score_for_panhard", "coverage_with_filter_panhard")):
            xlabel = "Remaining file count"
            fig.update_xaxes(autorange="reversed", row=row, col=1)
        else:
            xlabel = {"score_per_measure": "Dataset", "measure_per_set": "Measure"}.get(
                exp.type
            )
        fig.update_xaxes(title_text=xlabel, automargin=True, row=row, col=1)
        if stops.get(key) is not None:
            fig.add_vline(x=stops[key], line_dash="dash", row=row, col=1)
        axis = "yaxis" + (str(row) if row > 1 else "")
        values = [v for trace in traces for v in (trace.y or ()) if v is not None]
        for trace in traces:
            error = getattr(trace, "error_y", None)
            if error and error.array:
                for y, delta in zip(trace.y, error.array):
                    if y is not None:
                        values.extend([y - delta, y + delta])
        limits = [0, upper]
        if values:
            lo, hi = min(values), max(values)
            pad = max((hi - lo) * 0.05, upper * 0.001)
            limits = [lo - pad, hi + pad]
        fit[axis + ".range"] = limits
        full[axis + ".range"] = [0, upper]
        fig.update_yaxes(range=limits, row=row, col=1)
    title = f"{exp.title} · {missing} missing executions"
    if partial:
        title += f" · {partial} partial executions"
    fig.update_layout(
        title=title,
        margin=dict(t=125),
        boxmode="group",
        height=max(480, len(panels) * 340),
        showlegend=exp.type != "score_per_measure",
        updatemenus=[
            dict(
                type="buttons",
                direction="right",
                x=1,
                xanchor="right",
                y=1,
                yanchor="bottom",
                pad=dict(b=32),
                buttons=[
                    dict(label="Fit to data", method="relayout", args=[fit]),
                    dict(label="Full range", method="relayout", args=[full]),
                ],
            )
        ],
    )
    return fig


def render(experiment, results_dir: Path, output_dir: Path):
    cells = collect_cells(experiment, results_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    build_figure(experiment, cells).write_html(
        output_dir / f"{experiment.id}.html",
        include_plotlyjs="directory",
        auto_open=False,
    )
