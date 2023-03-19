include "wo.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "orbi12d.mm"
include "sbor.mm"
include "vtoclbg.mm"

theorem sbcorgOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) )

  proof
    wph
    wps
    wo
    #
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wo
    @0
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wo
    vy
    cA
    cV
    @0
    vx
    vy
    cA
    dfsbcq2
    vy
    cv
    cA
    wceq
    @1
    @3
    @2
    @4
    wph
    vx
    vy
    cA
    dfsbcq2
    wps
    vx
    vy
    cA
    dfsbcq2
    orbi12d
    wph
    wps
    vx
    vy
    sbor
    vtoclbg
end
