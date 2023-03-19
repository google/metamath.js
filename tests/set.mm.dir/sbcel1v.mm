include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cvv.mm"
include "sbcex.mm"
include "elex.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "eleq1.mm"
include "clelsb3.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcel1v
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( [. A / x ]. x e. B <-> A e. B )

  proof
    vx
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
    cA
    cB
    wcel
    #
    @0
    vx
    cA
    sbcex
    cA
    cB
    elex
    @0
    vx
    vy
    wsb
    vy
    cv
    #
    cB
    wcel
    @1
    @2
    vy
    cA
    cvv
    @0
    vx
    vy
    cA
    dfsbcq2
    @3
    cA
    cB
    eleq1
    vy
    vx
    cB
    clelsb3
    vtoclbg
    pm5.21nii
end
