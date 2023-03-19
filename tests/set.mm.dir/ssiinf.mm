include "cv.mm"
include "ciin.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "ralbii.mm"
include "nfcv.mm"
include "ralcomf.mm"
include "bitri.mm"
include "dfss3.mm"
include "3bitr4i.mm"

theorem ssiinf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume ssiinf.1: |- F/_ x C


  assert |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B )

  proof
    vy
    cv
    #
    vx
    cA
    cB
    ciin
    #
    wcel
    #
    vy
    cC
    wral
    #
    @0
    cB
    wcel
    #
    vy
    cC
    wral
    #
    vx
    cA
    wral
    #
    cC
    @1
    wss
    cC
    cB
    wss
    #
    vx
    cA
    wral
    @3
    @4
    vx
    cA
    wral
    #
    vy
    cC
    wral
    @6
    @2
    @8
    vy
    cC
    @0
    cvv
    wcel
    @2
    @8
    wb
    vy
    vex
    vx
    @0
    cA
    cB
    cvv
    eliin
    ax-mp
    ralbii
    @4
    vy
    vx
    cC
    cA
    ssiinf.1
    vy
    cA
    nfcv
    ralcomf
    bitri
    vy
    cC
    @1
    dfss3
    @7
    @5
    vx
    cA
    vy
    cC
    cB
    dfss3
    ralbii
    3bitr4i
end
