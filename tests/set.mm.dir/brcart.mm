include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "ccart.mm"
include "cep.mm"
include "cpprod.mm"
include "opex.mm"
include "df-cart.mm"
include "wbr.mm"
include "wcel.mm"
include "opelvv.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "3anass.mm"
include "epelc.mm"
include "anbi12i.mm"
include "anbi2i.mm"
include "bitri.mm"
include "2exbii.mm"
include "vex.mm"
include "brpprod3b.mm"
include "elxp.mm"
include "3bitr4ri.mm"
include "brtxpsd3.mm"

theorem brcart
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume brcart.1: |- A e. _V
  assume brcart.2: |- B e. _V
  assume brcart.3: |- C e. _V


  assert |- ( <. A , B >. Cart C <-> C = ( A X. B ) )

  proof
    vx
    cA
    cB
    cop
    #
    cC
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    ccart
    cep
    cep
    cpprod
    #
    cA
    cB
    cxp
    #
    cA
    cB
    opex
    brcart.3
    df-cart
    @0
    cC
    @2
    wbr
    @0
    @1
    wcel
    cC
    cvv
    wcel
    cA
    cB
    brcart.1
    brcart.2
    opelvv
    brcart.3
    @0
    cC
    @1
    cvv
    brxp
    mpbir2an
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cop
    wceq
    #
    @6
    cA
    cep
    wbr
    #
    @7
    cB
    cep
    wbr
    #
    w3a
    #
    vz
    wex
    vy
    wex
    @8
    @6
    cA
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    @5
    @0
    @3
    wbr
    @5
    @4
    wcel
    @11
    @15
    vy
    vz
    @11
    @8
    @9
    @10
    wa
    #
    wa
    @15
    @8
    @9
    @10
    3anass
    @16
    @14
    @8
    @9
    @12
    @10
    @13
    @6
    cA
    brcart.1
    epelc
    @7
    cB
    brcart.2
    epelc
    anbi12i
    anbi2i
    bitri
    2exbii
    vy
    vz
    cep
    cep
    @5
    cA
    cB
    vx
    vex
    brcart.1
    brcart.2
    brpprod3b
    vy
    vz
    @5
    cA
    cB
    elxp
    3bitr4ri
    brtxpsd3
end
