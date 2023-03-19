include "cop.mm"
include "ctxp.mm"
include "wbr.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "wa.mm"
include "df-txp.mm"
include "breqi.mm"
include "brin.mm"
include "cv.mm"
include "wex.mm"
include "wceq.mm"
include "opex.mm"
include "brco.mm"
include "ancom.mm"
include "vex.mm"
include "brcnv.mm"
include "wcel.mm"
include "opelvv.mm"
include "brres.mm"
include "mpbiran2.mm"
include "br1steq.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "bitri.mm"
include "exbii.mm"
include "breq2.mm"
include "ceqsexv.mm"
include "br2ndeq.mm"
include "anbi12i.mm"

theorem brtxp
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  assume brtxp.1: |- X e. _V
  assume brtxp.2: |- Y e. _V
  assume brtxp.3: |- Z e. _V


  assert |- ( X ( A (x) B ) <. Y , Z >. <-> ( X A Y /\ X B Z ) )

  proof
    cX
    cY
    cZ
    cop
    #
    cA
    cB
    ctxp
    #
    wbr
    cX
    @0
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    #
    cA
    ccom
    #
    c2nd
    @2
    cres
    #
    ccnv
    #
    cB
    ccom
    #
    cin
    #
    wbr
    cX
    @0
    @5
    wbr
    #
    cX
    @0
    @8
    wbr
    #
    wa
    cX
    cY
    cA
    wbr
    #
    cX
    cZ
    cB
    wbr
    #
    wa
    cX
    @0
    @1
    @9
    cA
    cB
    df-txp
    breqi
    cX
    @0
    @5
    @8
    brin
    @10
    @12
    @11
    @13
    @10
    cX
    vy
    cv
    #
    cA
    wbr
    #
    @14
    @0
    @4
    wbr
    #
    wa
    #
    vy
    wex
    @14
    cY
    wceq
    #
    @15
    wa
    #
    vy
    wex
    @12
    vy
    cX
    @0
    @4
    cA
    brtxp.1
    cY
    cZ
    opex
    #
    brco
    @17
    @19
    vy
    @17
    @16
    @15
    wa
    @19
    @15
    @16
    ancom
    @16
    @18
    @15
    @16
    @0
    @14
    @3
    wbr
    #
    @0
    @14
    c1st
    wbr
    #
    @18
    @14
    @0
    @3
    vy
    vex
    #
    @20
    brcnv
    @21
    @22
    @0
    @2
    wcel
    #
    cY
    cZ
    brtxp.2
    brtxp.3
    opelvv
    #
    @0
    @14
    c1st
    @2
    @23
    brres
    mpbiran2
    cY
    cZ
    @14
    brtxp.2
    brtxp.3
    br1steq
    3bitri
    anbi1i
    bitri
    exbii
    @15
    @12
    vy
    cY
    brtxp.2
    @14
    cY
    cX
    cA
    breq2
    ceqsexv
    3bitri
    @11
    cX
    vz
    cv
    #
    cB
    wbr
    #
    @26
    @0
    @7
    wbr
    #
    wa
    #
    vz
    wex
    @26
    cZ
    wceq
    #
    @27
    wa
    #
    vz
    wex
    @13
    vz
    cX
    @0
    @7
    cB
    brtxp.1
    @20
    brco
    @29
    @31
    vz
    @29
    @28
    @27
    wa
    @31
    @27
    @28
    ancom
    @28
    @30
    @27
    @28
    @0
    @26
    @6
    wbr
    #
    @0
    @26
    c2nd
    wbr
    #
    @30
    @26
    @0
    @6
    vz
    vex
    #
    @20
    brcnv
    @32
    @33
    @24
    @25
    @0
    @26
    c2nd
    @2
    @34
    brres
    mpbiran2
    cY
    cZ
    @26
    brtxp.2
    brtxp.3
    br2ndeq
    3bitri
    anbi1i
    bitri
    exbii
    @27
    @13
    vz
    cZ
    brtxp.3
    @26
    cZ
    cX
    cB
    breq2
    ceqsexv
    3bitri
    anbi12i
    3bitri
end
