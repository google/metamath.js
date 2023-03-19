include "wo.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "jaoi.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "orbi12d.mm"
include "sbor.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) )

  proof
    wph
    wps
    wo
    #
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
    #
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
    #
    @0
    vx
    cA
    sbcex
    @3
    @2
    @4
    wph
    vx
    cA
    sbcex
    wps
    vx
    cA
    sbcex
    jaoi
    @0
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
    @1
    @5
    vy
    cA
    cvv
    @0
    vx
    vy
    cA
    dfsbcq2
    vy
    cv
    cA
    wceq
    @6
    @3
    @7
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
    pm5.21nii
end
