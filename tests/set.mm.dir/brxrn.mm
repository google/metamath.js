include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cxrn.mm"
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
include "wb.mm"
include "df-xrn.mm"
include "breqi.mm"
include "a1i.mm"
include "brin.mm"
include "cv.mm"
include "wex.mm"
include "wceq.mm"
include "opex.mm"
include "brcog.mm"
include "mpan2.mm"
include "3ad2ant1.mm"
include "brcnvg.mm"
include "elv.mm"
include "opelvvg.mm"
include "biantrurd.mm"
include "brresALTV.mm"
include "syl6rbbr.mm"
include "br1steqg.mm"
include "bitrd.mm"
include "3adant1.mm"
include "syl5bb.mm"
include "anbi1cd.mm"
include "exbidv.mm"
include "breq2.mm"
include "ceqsexgv.mm"
include "3ad2ant2.mm"
include "3bitrd.mm"
include "br2ndeqg.mm"
include "3ad2ant3.mm"
include "anbi12d.mm"

theorem brxrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A ( R |X. S ) <. B , C >. <-> ( A R B /\ A S C ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cop
    #
    cR
    cS
    cxrn
    #
    wbr
    #
    cA
    @4
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    #
    cR
    ccom
    #
    c2nd
    @7
    cres
    #
    ccnv
    #
    cS
    ccom
    #
    cin
    #
    wbr
    #
    cA
    @4
    @10
    wbr
    #
    cA
    @4
    @13
    wbr
    #
    wa
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cC
    cS
    wbr
    #
    wa
    @6
    @15
    wb
    @3
    cA
    @4
    @5
    @14
    cR
    cS
    df-xrn
    breqi
    a1i
    @15
    @18
    wb
    @3
    cA
    @4
    @10
    @13
    brin
    a1i
    @3
    @16
    @19
    @17
    @20
    @3
    @16
    cA
    vx
    cv
    #
    cR
    wbr
    #
    @21
    @4
    @9
    wbr
    #
    wa
    #
    vx
    wex
    #
    @21
    cB
    wceq
    #
    @22
    wa
    #
    vx
    wex
    #
    @19
    @0
    @1
    @16
    @25
    wb
    #
    @2
    @0
    @4
    cvv
    wcel
    #
    @29
    cB
    cC
    opex
    #
    vx
    cA
    @4
    @9
    cR
    cV
    cvv
    brcog
    mpan2
    3ad2ant1
    @3
    @24
    @27
    vx
    @3
    @23
    @26
    @22
    @23
    @4
    @21
    @8
    wbr
    #
    @3
    @26
    @23
    @32
    wb
    #
    vx
    @21
    cvv
    wcel
    @30
    @33
    @31
    @21
    @4
    cvv
    cvv
    @8
    brcnvg
    mpan2
    elv
    @1
    @2
    @32
    @26
    wb
    @0
    @1
    @2
    wa
    #
    @32
    @4
    @21
    c1st
    wbr
    #
    @26
    @34
    @35
    @4
    @7
    wcel
    #
    @35
    wa
    #
    @32
    @34
    @36
    @35
    cB
    cC
    cW
    cX
    opelvvg
    #
    biantrurd
    @32
    @37
    wb
    vx
    @7
    @4
    @21
    c1st
    cvv
    brresALTV
    elv
    syl6rbbr
    cB
    cC
    @21
    cW
    cX
    br1steqg
    bitrd
    3adant1
    syl5bb
    anbi1cd
    exbidv
    @1
    @0
    @28
    @19
    wb
    @2
    @22
    @19
    vx
    cB
    cW
    @21
    cB
    cA
    cR
    breq2
    ceqsexgv
    3ad2ant2
    3bitrd
    @3
    @17
    cA
    vy
    cv
    #
    cS
    wbr
    #
    @39
    @4
    @12
    wbr
    #
    wa
    #
    vy
    wex
    #
    @39
    cC
    wceq
    #
    @40
    wa
    #
    vy
    wex
    #
    @20
    @0
    @1
    @17
    @43
    wb
    #
    @2
    @0
    @30
    @47
    @31
    vy
    cA
    @4
    @12
    cS
    cV
    cvv
    brcog
    mpan2
    3ad2ant1
    @3
    @42
    @45
    vy
    @3
    @41
    @44
    @40
    @41
    @4
    @39
    @11
    wbr
    #
    @3
    @44
    @41
    @48
    wb
    #
    vy
    @39
    cvv
    wcel
    @30
    @49
    @31
    @39
    @4
    cvv
    cvv
    @11
    brcnvg
    mpan2
    elv
    @1
    @2
    @48
    @44
    wb
    @0
    @34
    @48
    @4
    @39
    c2nd
    wbr
    #
    @44
    @34
    @50
    @36
    @50
    wa
    #
    @48
    @34
    @36
    @50
    @38
    biantrurd
    @48
    @51
    wb
    vy
    @7
    @4
    @39
    c2nd
    cvv
    brresALTV
    elv
    syl6rbbr
    cB
    cC
    @39
    cW
    cX
    br2ndeqg
    bitrd
    3adant1
    syl5bb
    anbi1cd
    exbidv
    @2
    @0
    @46
    @20
    wb
    @1
    @40
    @20
    vy
    cC
    cX
    @39
    cC
    cA
    cS
    breq2
    ceqsexgv
    3ad2ant3
    3bitrd
    anbi12d
    3bitrd
end
