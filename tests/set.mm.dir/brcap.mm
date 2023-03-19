include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "ccap.mm"
include "c1st.mm"
include "ccnv.mm"
include "cep.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "opex.mm"
include "df-cap.mm"
include "wbr.mm"
include "wcel.mm"
include "opelvv.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "wel.mm"
include "epel.mm"
include "vex.mm"
include "brcnv.mm"
include "br1steq.mm"
include "bitri.mm"
include "anbi12ci.mm"
include "exbii.mm"
include "brco.mm"
include "clel3.mm"
include "3bitr4i.mm"
include "br2ndeq.mm"
include "anbi12i.mm"
include "brin.mm"
include "elin.mm"
include "3bitr4ri.mm"
include "brtxpsd3.mm"

theorem brcap
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume brcap.1: |- A e. _V
  assume brcap.2: |- B e. _V
  assume brcap.3: |- C e. _V


  assert |- ( <. A , B >. Cap C <-> C = ( A i^i B ) )

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
    ccap
    c1st
    ccnv
    #
    cep
    ccom
    #
    c2nd
    ccnv
    #
    cep
    ccom
    #
    cin
    #
    cA
    cB
    cin
    #
    cA
    cB
    opex
    #
    brcap.3
    df-cap
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
    brcap.1
    brcap.2
    opelvv
    brcap.3
    @0
    cC
    @1
    cvv
    brxp
    mpbir2an
    vx
    cv
    #
    @0
    @4
    wbr
    #
    @10
    @0
    @6
    wbr
    #
    wa
    @10
    cA
    wcel
    #
    @10
    cB
    wcel
    #
    wa
    @10
    @0
    @7
    wbr
    @10
    @8
    wcel
    @11
    @13
    @12
    @14
    @10
    vy
    cv
    #
    cep
    wbr
    #
    @15
    @0
    @3
    wbr
    #
    wa
    #
    vy
    wex
    @15
    cA
    wceq
    #
    vx
    vy
    wel
    #
    wa
    #
    vy
    wex
    @11
    @13
    @18
    @21
    vy
    @16
    @20
    @17
    @19
    vx
    vy
    epel
    #
    @17
    @0
    @15
    c1st
    wbr
    @19
    @15
    @0
    c1st
    vy
    vex
    #
    @9
    brcnv
    cA
    cB
    @15
    brcap.1
    brcap.2
    br1steq
    bitri
    anbi12ci
    exbii
    vy
    @10
    @0
    @3
    cep
    vx
    vex
    #
    @9
    brco
    vy
    @10
    cA
    brcap.1
    clel3
    3bitr4i
    @16
    @15
    @0
    @5
    wbr
    #
    wa
    #
    vy
    wex
    @15
    cB
    wceq
    #
    @20
    wa
    #
    vy
    wex
    @12
    @14
    @26
    @28
    vy
    @16
    @20
    @25
    @27
    @22
    @25
    @0
    @15
    c2nd
    wbr
    @27
    @15
    @0
    c2nd
    @23
    @9
    brcnv
    cA
    cB
    @15
    brcap.1
    brcap.2
    br2ndeq
    bitri
    anbi12ci
    exbii
    vy
    @10
    @0
    @5
    cep
    @24
    @9
    brco
    vy
    @10
    cB
    brcap.2
    clel3
    3bitr4i
    anbi12i
    @10
    @0
    @4
    @6
    brin
    @10
    cA
    cB
    elin
    3bitr4ri
    brtxpsd3
end
