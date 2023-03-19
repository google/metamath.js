include "cv.mm"
include "wsbc.mm"
include "crab.mm"
include "dfsbcq.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "sbceq1a.mm"
include "cbvrab.mm"
include "elrab2.mm"

theorem elrabsf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume elrabsf.1: |- F/_ x B


  assert |- ( A e. { x e. B | ph } <-> ( A e. B /\ [. A / x ]. ph ) )

  proof
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    wph
    vx
    cA
    wsbc
    vy
    cA
    cB
    wph
    vx
    cB
    crab
    wph
    vx
    @0
    cA
    dfsbcq
    wph
    @1
    vx
    vy
    cB
    elrabsf.1
    vy
    cB
    nfcv
    wph
    vy
    nfv
    wph
    vx
    @0
    nfsbc1v
    wph
    vx
    @0
    sbceq1a
    cbvrab
    elrab2
end
