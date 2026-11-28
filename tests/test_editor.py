import json
from threading import Thread
from urllib.error import HTTPError
from urllib.request import urlopen

import pytest
from experiment_runner.editor import editor_server


def test_editor_catalog_and_download_validation_leave_original_untouched(tmp_path):
    for d in ("datasets/used", "datasets/other", "tools/test-measure"):
        (tmp_path / d).mkdir(parents=True)
    entry = dict(
        id="e",
        title="Example",
        type="score_per_measure",
        runtime_clusters=[dict(datasets=["used"], tools=["test-measure"])],
    )
    original = json.dumps({"experiments": [entry]}).encode()
    config = tmp_path / "experiments.json"
    config.write_bytes(original)
    with editor_server(tmp_path) as server:
        thread = Thread(target=server.serve_forever)
        thread.start()
        try:
            base = f"http://127.0.0.1:{server.server_port}"
            with urlopen(base + "/config") as response:
                assert response.read() == original
            with urlopen(base + "/catalog") as response:
                assert json.load(response)["datasets"] == ["other", "used"]
            with urlopen(base + "/validate", data=original) as response:
                assert response.status == 200
            entry["runtime_clusters"] *= 2
            with pytest.raises(HTTPError) as error:
                urlopen(
                    base + "/validate",
                    data=json.dumps({"experiments": [entry]}).encode(),
                )
            assert error.value.code == 400 and b"overlap" in error.value.read()
            assert config.read_bytes() == original
        finally:
            server.shutdown()
            thread.join()
