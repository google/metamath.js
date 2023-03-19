include "wa.mm"
include "simpr.mm"
include "bnj593.mm"

theorem bnj1266
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj1266.1: |- ( ch -> E. x ( ph /\ ps ) )


  assert |- ( ch -> E. x ps )

  proof
    wch
    wph
    wps
    wa
    wps
    vx
    bnj1266.1
    wph
    wps
    simpr
    bnj593
end
