include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "nfra1.mm"
include "nfcri.mm"
include "eleq1.mm"
include "vex.mm"
include "a1i.mm"
include "rspa.mm"
include "elabreximd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem abrexss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  assume abrexss.1: |- F/_ x C

  disjoint x y
  disjoint A y
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint C z
  disjoint B z
  assert |- ( A. x e. A B e. C -> { y | E. x e. A y = B } C_ C )

  proof
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vz
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cC
    @1
    vz
    cv
    #
    @2
    wcel
    @3
    cC
    wcel
    #
    @1
    @0
    @4
    vx
    vy
    @3
    cB
    cA
    cvv
    @0
    vx
    cA
    nfra1
    vx
    vz
    cC
    abrexss.1
    nfcri
    @3
    cB
    cC
    eleq1
    @3
    cvv
    wcel
    @1
    vz
    vex
    a1i
    @0
    vx
    cA
    rspa
    elabreximd
    ex
    ssrdv
end
