include "wex.mm"
include "19.9h.mm"
include "sylib.mm"

theorem bnj1397
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bnj1397.1: |- ( ph -> E. x ps )
  assume bnj1397.2: |- ( ps -> A. x ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    vx
    wex
    wps
    bnj1397.1
    wps
    vx
    bnj1397.2
    19.9h
    sylib
end
