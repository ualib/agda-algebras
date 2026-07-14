---
title: Module constellation
hide:
  - toc
---

# Module constellation

The library as a sky: every **star is a module**, sized by how many other modules
import it; every **line is an import**.  Colour marks the top-level tree.  Drag a
star, scroll to zoom, hover to trace its neighbourhood, and click to open the
module.

<div class="constellation-legend">
  <span><i style="background:#e0a458"></i>Overture</span>
  <span><i style="background:#46c7b8"></i>Setoid</span>
  <span><i style="background:#e0815a"></i>Classical</span>
  <span><i style="background:#b48ce0"></i>Order</span>
  <span><i style="background:#84c97f"></i>Examples</span>
  <span><i style="background:#e88bbf"></i>Exercises</span>
  <span><i style="background:#8c968f"></i>Legacy</span>
</div>

<div id="constellation"></div>

<p class="constellation-note">
  The brightest stars — <code>Overture</code>, <code>Setoid.Algebras.Basic</code>,
  <code>Overture.Terms</code> — are the foundations the rest of the library is
  built upon.
</p>

<script src="/assets/js/d3.v7.min.js"></script>
<script src="/assets/js/constellation.js"></script>
