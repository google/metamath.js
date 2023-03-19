include "wex.mm"
include "19.9v.mm"
include "sylib.mm"

theorem bnj937
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bnj937.1: |- ( ph -> E. x ps )

  disjoint ps x
  assert |- ( ph -> ps )

  proof
    wph
    wps
    vx
    wex
    wps
    bnj937.1
    wps
    vx
    19.9v
    sylib
end
