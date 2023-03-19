include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "ccup.mm"
include "c1st.mm"
include "ccnv.mm"
include "cep.mm"
include "ccom.mm"
include "c2nd.mm"
include "cun.mm"
include "opex.mm"
include "df-cup.mm"
include "wbr.mm"
include "wcel.mm"
include "opelvv.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "cv.mm"
include "wo.mm"
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
include "orbi12i.mm"
include "brun.mm"
include "elun.mm"
include "3bitr4ri.mm"
include "brtxpsd3.mm"

theorem brcup
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume brcup.1: |- A e. _V
  assume brcup.2: |- B e. _V
  assume brcup.3: |- C e. _V


  assert |- ( <. A , B >. Cup C <-> C = ( A u. B ) )

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
    ccup
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
    cun
    #
    cA
    cB
    cun
    #
    cA
    cB
    opex
    #
    brcup.3
    df-cup
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
    brcup.1
    brcup.2
    opelvv
    brcup.3
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
    wo
    @10
    cA
    wcel
    #
    @10
    cB
    wcel
    #
    wo
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
    brcup.1
    brcup.2
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
    brcup.1
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
    brcup.1
    brcup.2
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
    brcup.2
    clel3
    3bitr4i
    orbi12i
    @10
    @0
    @4
    @6
    brun
    @10
    cA
    cB
    elun
    3bitr4ri
    brtxpsd3
end
