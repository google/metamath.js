include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "sbcex.mm"
include "exsimpl.mm"
include "isset.mm"
include "sylibr.mm"
include "wsb.mm"
include "weq.mm"
include "dfsbcq2.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "sb5.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbc5
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) )

  proof
    wph
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
    #
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    wph
    vx
    cA
    sbcex
    @5
    @3
    vx
    wex
    @1
    @3
    wph
    vx
    exsimpl
    vx
    cA
    isset
    sylibr
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    wph
    wa
    #
    vx
    wex
    @0
    @5
    vy
    cA
    cvv
    wph
    vx
    vy
    cA
    dfsbcq2
    vy
    cv
    #
    cA
    wceq
    #
    @7
    @4
    vx
    @9
    @6
    @3
    wph
    @8
    cA
    @2
    eqeq2
    anbi1d
    exbidv
    wph
    vx
    vy
    sb5
    vtoclbg
    pm5.21nii
end
