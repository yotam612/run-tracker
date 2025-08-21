# Run Progress Tracker

This project is a single-page tool for tracking run attempts, parts, and sessions.
Parts are defined by their percentage ranges, and practice runs are scheduled
automatically from recent part performance using a user‑set probability threshold.

## Structure
- `index.html` – main interface markup.
- `style.css` – styles for the interface.
- `script.js` – logic for data handling, rendering, scheduling, and storage.

Open `index.html` in a browser to use the tracker. Runs are displayed in the Sessions tab and omitted from Trends. The Trends chart can limit displayed batches (default 50) or show all.
