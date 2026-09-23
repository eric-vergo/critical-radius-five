#!/usr/bin/env bash
# Render every scene: 1080p60 MP4, a GIF preview, and two stills of the final frame
# (dark theme, and light theme for the paper's figures).
#
#   ./render.sh                 # all scenes
#   ./render.sh B2Levels ...    # only the named scenes
#
# Needs Manim Community 0.21 (+ LaTeX) and ffmpeg.  Set MANIM to the manim executable if it is
# not on PATH, e.g.  MANIM=~/.venvs/manim/bin/manim ./render.sh
set -euo pipefail
cd "$(dirname "$0")"

MANIM=${MANIM:-manim}
PYTHON=${PYTHON:-$(dirname "$(command -v "$MANIM")")/python}
QUALITY=${QUALITY:--qh}          # -qh = 1920x1080, 60 fps
BUILD=build                      # manim working directories (not committed)
OUT=renders
mkdir -p "$OUT/mp4" "$OUT/gif" "$OUT/stills/dark" "$OUT/stills/light" ../paper/figures

# scene-file  scene-class  output-name
SCENES=(
  "scenes/a1_setting.py   A1Setting    a1_setting"
  "scenes/a2_a4_words.py  A2WordOne    a2_word1"
  "scenes/a2_a4_words.py  A3WordTwo    a3_word2"
  "scenes/a2_a4_words.py  A4WordThree  a4_word3"
  "scenes/a5_exchange.py  A5Exchange   a5_exchange"
  "scenes/b1_lattice.py   B1Lattice    b1_lattice"
  "scenes/b2_levels.py    B2Levels     b2_levels"
  "scenes/b3_threshold.py B3Threshold  b3_threshold"
  "scenes/b4_monotone.py  B4Monotone   b4_monotone"
)

wanted() {
  [ $# -eq 0 ] && return 0
  local s
  for s in "${ONLY[@]}"; do [ "$s" = "$1" ] && return 0; done
  return 1
}
ONLY=("$@")

for entry in "${SCENES[@]}"; do
  read -r file cls name <<<"$entry"
  if [ ${#ONLY[@]} -gt 0 ] && ! wanted "$cls"; then continue; fi
  module=$(basename "$file" .py)
  echo "=== $cls -> $name"

  # 1. the video (dark theme)
  GG5_THEME=dark "$MANIM" "$QUALITY" --media_dir "$BUILD/dark" -o "$name" "$file" "$cls"
  mp4=$(ls -t "$BUILD"/dark/videos/"$module"/*/"$name".mp4 | head -1)
  cp "$mp4" "$OUT/mp4/$name.mp4"

  # 2. the GIF preview: 1280 px wide, 12 fps (10 fps if that would exceed 25 MB), optimised palette
  gif="$OUT/gif/$name.gif"
  for fps in 12 10; do
    ffmpeg -loglevel error -y -i "$OUT/mp4/$name.mp4" -vf \
      "fps=$fps,scale=1280:-1:flags=lanczos,split[a][b];[a]palettegen=max_colors=256:stats_mode=diff[p];[b][p]paletteuse=dither=bayer:bayer_scale=4:diff_mode=rectangle" \
      -loop 0 "$gif"
    size=$(( $(wc -c < "$gif") ))
    echo "  $name.gif: $fps fps, $size bytes"
    [ "$size" -le $((25 * 1024 * 1024)) ] && break
  done

  # 3. the last frame as a still, in both themes
  for theme in dark light; do
    GG5_THEME=$theme "$MANIM" "$QUALITY" -s --media_dir "$BUILD/still-$theme" -o "$name" "$file" "$cls"
    png=$(ls -t "$BUILD"/still-"$theme"/images/"$module"/"$name"*.png | head -1)
    cp "$png" "$OUT/stills/$theme/$name.png"
  done
done
# 4. the paper's figures: crops of the light stills
"$PYTHON" crop_figures.py
echo "done."
