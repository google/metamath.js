include "cres.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "wbr.mm"
include "wrex.mm"
include "dfss3.mm"
include "ssrnres.mm"
include "cima.mm"
include "df-ima.mm"
include "eleq2i.mm"
include "vex.mm"
include "elima.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "3bitr3i.mm"

theorem rninxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ran ( C i^i ( A X. B ) ) = B <-> A. y e. B E. x e. A x C y )

  proof
    cB
    cC
    cA
    cres
    crn
    #
    wss
    vy
    cv
    #
    @0
    wcel
    #
    vy
    cB
    wral
    cC
    cA
    cB
    cxp
    cin
    crn
    cB
    wceq
    vx
    cv
    @1
    cC
    wbr
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    vy
    cB
    @0
    dfss3
    cA
    cB
    cC
    ssrnres
    @2
    @3
    vy
    cB
    @2
    @1
    cC
    cA
    cima
    #
    wcel
    @3
    @4
    @0
    @1
    cC
    cA
    df-ima
    eleq2i
    vx
    @1
    cC
    cA
    vy
    vex
    elima
    bitr3i
    ralbii
    3bitr3i
end
