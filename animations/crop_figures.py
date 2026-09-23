"""Crop the light-theme stills into the figures used by the paper (paper/figures/)."""
from pathlib import Path

from PIL import Image

HERE = Path(__file__).resolve().parent
SRC = HERE / "renders" / "stills" / "light"
DST = HERE.parent / "paper" / "figures"

# crop boxes in scene coordinates (x0, y0, x1, y1); the frame is [-64/9, 64/9] x [-4, 4]
BOXES = {
    "a1_setting": (-6.25, -3.08, 2.3, 2.75),
    "a2_word1": (-6.25, -3.3, 2.3, 2.7),
    "a3_word2": (-6.25, -3.3, 2.3, 2.7),
    "a4_word3": (-6.25, -3.3, 2.3, 2.7),
    "a5_exchange": (-0.35, -3.6, 7.11, 3.05),
    "b1_lattice": (-6.4, -3.45, 0.2, 2.75),
    "b2_levels": (-0.78, -4.0, 7.11, 2.25),
    "b3_threshold": (-7.11, -4.0, 7.11, 3.25),
    "b4_monotone": (-6.8, -3.6, -0.1, 2.9),
}


def crop(name, box):
    im = Image.open(SRC / f"{name}.png")
    w, h = im.size
    s = h / 8.0
    x0, y0, x1, y1 = box
    px = lambda x: int(round((x + w / (2 * s)) * s))
    py = lambda y: int(round((4.0 - y) * s))
    im.crop((max(px(x0), 0), max(py(y1), 0), min(px(x1), w), min(py(y0), h))).save(
        DST / f"{name}.png", optimize=True)


if __name__ == "__main__":
    DST.mkdir(parents=True, exist_ok=True)
    for name, box in BOXES.items():
        if (SRC / f"{name}.png").exists():
            crop(name, box)
            print("cropped", name)
