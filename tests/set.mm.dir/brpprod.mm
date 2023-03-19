include "cop.mm"
include "cpprod.mm"
include "wbr.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccom.mm"
include "c2nd.mm"
include "ctxp.mm"
include "wa.mm"
include "df-pprod.mm"
include "breqi.mm"
include "opex.mm"
include "brtxp.mm"
include "cv.mm"
include "wex.mm"
include "wceq.mm"
include "brco.mm"
include "wcel.mm"
include "opelvv.mm"
include "vex.mm"
include "brres.mm"
include "mpbiran2.mm"
include "br1steq.mm"
include "bitri.mm"
include "anbi1i.mm"
include "exbii.mm"
include "breq1.mm"
include "ceqsexv.mm"
include "3bitri.mm"
include "br2ndeq.mm"
include "anbi12i.mm"

theorem brpprod
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume brpprod.1: |- X e. _V
  assume brpprod.2: |- Y e. _V
  assume brpprod.3: |- Z e. _V
  assume brpprod.4: |- W e. _V


  assert |- ( <. X , Y >. pprod ( A , B ) <. Z , W >. <-> ( X A Z /\ Y B W ) )

  proof
    cX
    cY
    cop
    #
    cZ
    cW
    cop
    #
    cA
    cB
    cpprod
    #
    wbr
    @0
    @1
    cA
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccom
    #
    cB
    c2nd
    @3
    cres
    #
    ccom
    #
    ctxp
    #
    wbr
    @0
    cZ
    @5
    wbr
    #
    @0
    cW
    @7
    wbr
    #
    wa
    cX
    cZ
    cA
    wbr
    #
    cY
    cW
    cB
    wbr
    #
    wa
    @0
    @1
    @2
    @8
    cA
    cB
    df-pprod
    breqi
    @5
    @7
    @0
    cZ
    cW
    cX
    cY
    opex
    #
    brpprod.3
    brpprod.4
    brtxp
    @9
    @11
    @10
    @12
    @9
    @0
    vx
    cv
    #
    @4
    wbr
    #
    @14
    cZ
    cA
    wbr
    #
    wa
    #
    vx
    wex
    @14
    cX
    wceq
    #
    @16
    wa
    #
    vx
    wex
    @11
    vx
    @0
    cZ
    cA
    @4
    @13
    brpprod.3
    brco
    @17
    @19
    vx
    @15
    @18
    @16
    @15
    @0
    @14
    c1st
    wbr
    #
    @18
    @15
    @20
    @0
    @3
    wcel
    #
    cX
    cY
    brpprod.1
    brpprod.2
    opelvv
    #
    @0
    @14
    c1st
    @3
    vx
    vex
    brres
    mpbiran2
    cX
    cY
    @14
    brpprod.1
    brpprod.2
    br1steq
    bitri
    anbi1i
    exbii
    @16
    @11
    vx
    cX
    brpprod.1
    @14
    cX
    cZ
    cA
    breq1
    ceqsexv
    3bitri
    @10
    @0
    vy
    cv
    #
    @6
    wbr
    #
    @23
    cW
    cB
    wbr
    #
    wa
    #
    vy
    wex
    @23
    cY
    wceq
    #
    @25
    wa
    #
    vy
    wex
    @12
    vy
    @0
    cW
    cB
    @6
    @13
    brpprod.4
    brco
    @26
    @28
    vy
    @24
    @27
    @25
    @24
    @0
    @23
    c2nd
    wbr
    #
    @27
    @24
    @29
    @21
    @22
    @0
    @23
    c2nd
    @3
    vy
    vex
    brres
    mpbiran2
    cX
    cY
    @23
    brpprod.1
    brpprod.2
    br2ndeq
    bitri
    anbi1i
    exbii
    @25
    @12
    vy
    cY
    brpprod.2
    @23
    cY
    cW
    cB
    breq1
    ceqsexv
    3bitri
    anbi12i
    3bitri
end
