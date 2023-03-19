include "wa.mm"
include "bnj596.mm"
include "bnj1198.mm"

theorem bnj1340
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume bnj1340.1: |- ( ps -> E. x th )
  assume bnj1340.2: |- ( ch <-> ( ps /\ th ) )
  assume bnj1340.3: |- ( ps -> A. x ps )


  assert |- ( ps -> E. x ch )

  proof
    wps
    wps
    wth
    wa
    vx
    wch
    wps
    wth
    vx
    bnj1340.3
    bnj1340.1
    bnj596
    bnj1340.2
    bnj1198
end
