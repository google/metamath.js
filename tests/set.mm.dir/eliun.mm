include "ciun.mm"
include "wcel.mm"
include "cvv.mm"
include "wrex.mm"
include "elex.mm"
include "rexlimivw.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "rexbidv.mm"
include "df-iun.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem eliun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A e. U_ x e. B C <-> E. x e. B A e. C )

  proof
    cA
    vx
    cB
    cC
    ciun
    #
    wcel
    cA
    cvv
    wcel
    #
    cA
    cC
    wcel
    #
    vx
    cB
    wrex
    #
    cA
    @0
    elex
    @2
    @1
    vx
    cB
    cA
    cC
    elex
    rexlimivw
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cB
    wrex
    @3
    vy
    cA
    @0
    cvv
    @4
    cA
    wceq
    @5
    @2
    vx
    cB
    @4
    cA
    cC
    eleq1
    rexbidv
    vx
    vy
    cB
    cC
    df-iun
    elab2g
    pm5.21nii
end
