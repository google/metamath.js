include "wa.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "adantl.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "anbi12d.mm"
include "sban.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- ( [. A / x ]. ( ph /\ ps ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) )

  proof
    wph
    wps
    wa
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
    wa
    #
    @0
    vx
    cA
    sbcex
    @4
    @2
    @3
    wps
    vx
    cA
    sbcex
    adantl
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
    wa
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
    anbi12d
    wph
    wps
    vx
    vy
    sban
    vtoclbg
    pm5.21nii
end
