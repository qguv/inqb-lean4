#import "@preview/cetz:0.3.1"

#let transparent = rgb(0, 0, 0, 0)

#let _parse-wspec(spec) = {
  if spec == [ ] {
    " "
  } else if type(spec) == str {
    spec
  } else if spec.has("text") {
    spec.text
  } else if spec.has("children") {
    spec.children.map(_parse-wspec).join("")
  } else if spec.func() == smartquote {
    "'"
  }
}

#let show-wspec(spec) = {
  spec = _parse-wspec(spec)
    .split("|")
    .map(s => if s in ("", " ") { "  " } else { s })
    .join("|")
  text(font: "New Computer Modern Mono", "w[" + spec +"]")
}

#let w(
  spec,
  invert: false,
  bump-x: false,
  bump-y: false,
  colors: false,
  label: (:),
) = {
  let fg = if invert { white } else { black }
  let bg = if invert { black } else { white }

  let alts = _parse-wspec(spec)
  alts = if alts == none { () } else { alts.split("|") }
  alts = alts.filter(x => x not in ("", " ", "  "))

  box(baseline: 50%-.5em, cetz.canvas({
    import cetz.draw: *

    scale(0.1)

    // background
    rect((-1, -1), (12, 12), fill: bg, stroke: transparent)

    // maybe labels
    if "left" in label {
      content(
        (0, 8),
        anchor: "east",
        text(8pt, label.at("left"))
      )
      content(
        (0, 3),
        anchor: "east",
        text(8pt, math.not + label.at("left"))
      )
    }
    if "top" in label {
      content(
        (3, 12),
        text(8pt, label.at("top"))
      )
      content(
        (8, 12),
        text(8pt, math.not + label.at("top"))
      )
    }

    for (i, alt) in alts.enumerate() {
      let trans = (
        x: if bump-x { int(calc.odd(i)) * .5 - .25 } else { 0 },
        y: if bump-y { int(calc.odd(i)) * .5 - .25 } else { 0 },
      )

      // normalize
      let rot = (
        if alt in (" '", " :", "'.", ":.") {
          -90deg
        } else if alt in (" .", "..", ":'") {
          180deg
        } else if alt in (". ", ": ", "':") {
          90deg
        } else {
          0
        }
      )

      colors = (
        if type(colors) == array {
          colors
        } else if colors == true {
          (blue, purple, rgb(220, 100, 255), rgb(100, 100, 100))
        } else if colors == false {
          (fg,)
        } else {
          (colors,)
        }
      )
      
      let alt-color = colors.at(calc.rem(i, colors.len()))

      translate(..trans)
      rotate(origin: (5.5, 5.5), z: rot)

      // one world
      if alt in ("' ", " '", " .", ". ") {
        rect((1, 6), (5, 10), stroke: alt-color)
      }

      // two adjacent worlds
      if alt in ("''", " :", "..", ": ") {
        rect((1, 6), (10, 10), stroke: alt-color)
      }

      // two opposite worlds
      if alt in (".'", "'.") {
        line(
          stroke: alt-color,
          (1, 1),
          (1, 5),
          (5, 6), // zk top left
          (6, 10),
          (10, 10),
          (10, 6),
          (6, 5), // zk bottom right
          (5, 1),
          (1, 1),
          (1, 5), // prevent corner discontinuity
        )
      }

      // three worlds
      if alt in (".:", ":.", ":'", "':") {
        line(
          stroke: alt-color,
          (1, 1),
          (1, 5),
          (5, 6), // zk
          (6, 10),
          (10, 10),
          (10, 1),
          (1, 1),
          (1, 5), // prevent corner discontinuity
        )
      }

      // four worlds
      if alt == "::" {
        rect((1, 1), (10, 10), stroke: alt-color)
      }

      // reset bump and normalization
      rotate(origin: (5.5, 5.5), z: -rot)
      translate(x: -trans.x, y: -trans.y)
    }

    // worlds
    let c = (3, 8)
    for x in c {
      for y in c {
        circle((x, y), stroke: fg)
      }
    }

    if (alts.len() == 0) {
      content((5.5, 5.5), text(9pt, gray, math.emptyset))
    }

    if "::" in alts {
      rect((0, 0), (11, 11), stroke: fg)
    }
  }))
}

#let wc(spec, ..opts) = w(spec, colors: true, ..opts)
#let wx(spec, ..opts) = w(spec, bump-x: true, ..opts)
#let wcx(spec, ..opts) = w(spec, colors: true, bump-x: true, ..opts)
#let wy(spec, ..opts) = w(spec, bump-y: true, ..opts)
#let wcy(spec, ..opts) = w(spec, colors: true, bump-y: true, ..opts)
#let wxy(spec, ..opts) = w(spec, bump-x: true, bump-y: true, ..opts)
#let wcxy(spec, ..opts) = w(spec, colors: true, bump-x: true, bump-y: true, ..opts)