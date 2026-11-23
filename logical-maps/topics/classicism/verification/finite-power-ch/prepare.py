"""Expand the saved proof terms and check all Lean inputs before replay."""
import hashlib
import lzma
from pathlib import Path
from tempfile import NamedTemporaryFile

ROOT = Path(__file__).resolve().parent


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    records = (ROOT / "sources.sha256").read_text().splitlines()
    for record in records:
        expected, name = record.split("  ", 1)
        path = ROOT / name
        if path.is_file() and digest(path) == expected:
            continue
        archive = path.with_suffix(".json.xz")
        if path.suffix != ".json" or not archive.is_file():
            raise SystemExit(f"Missing or modified proof input: {name}")
        with NamedTemporaryFile(dir=path.parent, delete=False) as out:
            temp = Path(out.name)
        try:
            with lzma.open(archive, "rb") as src, temp.open("wb") as dst:
                while block := src.read(1024 * 1024):
                    dst.write(block)
            if digest(temp) != expected:
                raise SystemExit(f"Proof data does not match its recorded digest: {name}")
            temp.replace(path)
        finally:
            temp.unlink(missing_ok=True)
    print(f"Verified {len(records)} proof inputs.")


if __name__ == "__main__":
    main()
