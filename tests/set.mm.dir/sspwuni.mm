include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "cuni.mm"
include "selpw.mm"
include "ralbii.mm"
include "dfss3.mm"
include "unissb.mm"
include "3bitr4i.mm"

theorem sspwuni
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ ~P B <-> U. A C_ B )

  proof
    vx
    cv
    #
    cB
    cpw
    #
    wcel
    #
    vx
    cA
    wral
    @0
    cB
    wss
    #
    vx
    cA
    wral
    cA
    @1
    wss
    cA
    cuni
    cB
    wss
    @2
    @3
    vx
    cA
    vx
    cB
    selpw
    ralbii
    vx
    cA
    @1
    dfss3
    vx
    cA
    cB
    unissb
    3bitr4i
end
