include "cop.mm"
include "ccap.mm"
include "c1st.mm"
include "ccart.mm"
include "c2nd.mm"
include "crange.mm"
include "ccom.mm"
include "ctxp.mm"
include "wbr.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "crestrict.mm"
include "cres.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "opex.mm"
include "brco.mm"
include "w3a.mm"
include "brtxp2.mm"
include "3anrot.mm"
include "br1steq.mm"
include "vex.mm"
include "br2ndeq.mm"
include "anbi1i.mm"
include "exbii.mm"
include "breq1.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "brrange.mm"
include "3bitri.mm"
include "biid.mm"
include "3anbi123i.mm"
include "2exbii.mm"
include "rnex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "opeq2.mm"
include "ceqsex2v.mm"
include "brcart.mm"
include "xpex.mm"
include "brcap.mm"
include "df-restrict.mm"
include "breqi.mm"
include "dfres3.mm"
include "eqeq2i.mm"
include "3bitr4i.mm"

theorem brrestrict
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume brrestrict.1: |- A e. _V
  assume brrestrict.2: |- B e. _V
  assume brrestrict.3: |- C e. _V


  assert |- ( <. A , B >. Restrict C <-> C = ( A |` B ) )

  proof
    cA
    cB
    cop
    #
    cC
    ccap
    c1st
    ccart
    c2nd
    crange
    c1st
    ccom
    #
    ctxp
    #
    ccom
    #
    ctxp
    #
    ccom
    #
    wbr
    #
    cC
    cA
    cB
    cA
    crn
    #
    cxp
    #
    cin
    #
    wceq
    #
    @0
    cC
    crestrict
    wbr
    cC
    cA
    cB
    cres
    #
    wceq
    @6
    vx
    cv
    #
    cA
    @8
    cop
    #
    wceq
    #
    @12
    cC
    ccap
    wbr
    #
    wa
    #
    vx
    wex
    #
    @13
    cC
    ccap
    wbr
    #
    @10
    @6
    @0
    @12
    @4
    wbr
    #
    @15
    wa
    #
    vx
    wex
    @17
    vx
    @0
    cC
    ccap
    @4
    cA
    cB
    opex
    #
    brrestrict.3
    brco
    @20
    @16
    vx
    @19
    @14
    @15
    @19
    @12
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    @0
    @22
    c1st
    wbr
    #
    @0
    @23
    @3
    wbr
    #
    w3a
    #
    vb
    wex
    va
    wex
    @22
    cA
    wceq
    #
    @23
    @8
    wceq
    #
    @25
    w3a
    #
    vb
    wex
    va
    wex
    @14
    va
    vb
    @0
    @12
    c1st
    @3
    @21
    brtxp2
    @28
    @31
    va
    vb
    @28
    @26
    @27
    @25
    w3a
    @31
    @25
    @26
    @27
    3anrot
    @26
    @29
    @27
    @30
    @25
    @25
    cA
    cB
    @22
    brrestrict.1
    brrestrict.2
    br1steq
    @27
    @0
    @12
    @2
    wbr
    #
    @12
    @23
    ccart
    wbr
    #
    wa
    #
    vx
    wex
    #
    cB
    @7
    cop
    #
    @23
    ccart
    wbr
    #
    @30
    vx
    @0
    @23
    ccart
    @2
    @21
    vb
    vex
    #
    brco
    @35
    @12
    @36
    wceq
    #
    @33
    wa
    #
    vx
    wex
    @37
    @34
    @40
    vx
    @32
    @39
    @33
    @32
    @25
    @0
    @22
    c2nd
    wbr
    #
    @0
    @23
    @1
    wbr
    #
    w3a
    #
    vb
    wex
    va
    wex
    @22
    cB
    wceq
    #
    @23
    @7
    wceq
    #
    @25
    w3a
    #
    vb
    wex
    va
    wex
    @39
    va
    vb
    @0
    @12
    c2nd
    @1
    @21
    brtxp2
    @43
    @46
    va
    vb
    @43
    @41
    @42
    @25
    w3a
    @46
    @25
    @41
    @42
    3anrot
    @41
    @44
    @42
    @45
    @25
    @25
    cA
    cB
    @22
    brrestrict.1
    brrestrict.2
    br2ndeq
    @42
    @0
    @12
    c1st
    wbr
    #
    @12
    @23
    crange
    wbr
    #
    wa
    #
    vx
    wex
    #
    cA
    @23
    crange
    wbr
    #
    @45
    vx
    @0
    @23
    crange
    c1st
    @21
    @38
    brco
    @50
    @12
    cA
    wceq
    #
    @48
    wa
    #
    vx
    wex
    @51
    @49
    @53
    vx
    @47
    @52
    @48
    cA
    cB
    @12
    brrestrict.1
    brrestrict.2
    br1steq
    anbi1i
    exbii
    @48
    @51
    vx
    cA
    brrestrict.1
    @12
    cA
    @23
    crange
    breq1
    ceqsexv
    bitri
    cA
    @23
    brrestrict.1
    @38
    brrange
    3bitri
    @25
    biid
    #
    3anbi123i
    bitri
    2exbii
    @25
    @12
    cB
    @23
    cop
    #
    wceq
    @39
    va
    vb
    cB
    @7
    brrestrict.2
    cA
    brrestrict.1
    rnex
    #
    @44
    @24
    @55
    @12
    @22
    cB
    @23
    opeq1
    eqeq2d
    @45
    @55
    @36
    @12
    @23
    @7
    cB
    opeq2
    eqeq2d
    ceqsex2v
    3bitri
    anbi1i
    exbii
    @33
    @37
    vx
    @36
    cB
    @7
    opex
    @12
    @36
    @23
    ccart
    breq1
    ceqsexv
    bitri
    cB
    @7
    @23
    brrestrict.2
    @56
    @38
    brcart
    3bitri
    @54
    3anbi123i
    bitri
    2exbii
    @25
    @12
    cA
    @23
    cop
    #
    wceq
    @14
    va
    vb
    cA
    @8
    brrestrict.1
    cB
    @7
    brrestrict.2
    @56
    xpex
    #
    @29
    @24
    @57
    @12
    @22
    cA
    @23
    opeq1
    eqeq2d
    @30
    @57
    @13
    @12
    @23
    @8
    cA
    opeq2
    eqeq2d
    ceqsex2v
    3bitri
    anbi1i
    exbii
    bitri
    @15
    @18
    vx
    @13
    cA
    @8
    opex
    @12
    @13
    cC
    ccap
    breq1
    ceqsexv
    cA
    @8
    cC
    brrestrict.1
    @58
    brrestrict.3
    brcap
    3bitri
    @0
    cC
    crestrict
    @5
    df-restrict
    breqi
    @11
    @9
    cC
    cA
    cB
    dfres3
    eqeq2i
    3bitr4i
end
