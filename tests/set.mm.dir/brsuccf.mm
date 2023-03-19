include "csuccf.mm"
include "wbr.mm"
include "ccup.mm"
include "cid.mm"
include "csingle.mm"
include "ctxp.mm"
include "ccom.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "csuc.mm"
include "wceq.mm"
include "df-succf.mm"
include "breqi.mm"
include "brco.mm"
include "csn.mm"
include "cop.mm"
include "cun.mm"
include "opex.mm"
include "breq1.mm"
include "ceqsexv.mm"
include "snex.mm"
include "brcup.mm"
include "bitri.mm"
include "w3a.mm"
include "brtxp2.mm"
include "anbi1i.mm"
include "3anass.mm"
include "an32.mm"
include "vex.mm"
include "ideq.mm"
include "eqcom.mm"
include "brsingle.mm"
include "anbi12i.mm"
include "ancom.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "3bitri.mm"
include "2exbii.mm"
include "19.41vv.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "opeq2.mm"
include "ceqsex2v.mm"
include "3bitr3i.mm"
include "exbii.mm"
include "df-suc.mm"
include "eqeq2i.mm"

theorem brsuccf
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume brsuccf.1: |- A e. _V
  assume brsuccf.2: |- B e. _V


  assert |- ( A Succ B <-> B = suc A )

  proof
    cA
    cB
    csuccf
    wbr
    cA
    cB
    ccup
    cid
    csingle
    ctxp
    #
    ccom
    #
    wbr
    cA
    vx
    cv
    #
    @0
    wbr
    #
    @2
    cB
    ccup
    wbr
    #
    wa
    #
    vx
    wex
    #
    cB
    cA
    csuc
    #
    wceq
    #
    cA
    cB
    csuccf
    @1
    df-succf
    breqi
    vx
    cA
    cB
    ccup
    @0
    brsuccf.1
    brsuccf.2
    brco
    @2
    cA
    cA
    csn
    #
    cop
    #
    wceq
    #
    @4
    wa
    #
    vx
    wex
    #
    cB
    cA
    @9
    cun
    #
    wceq
    #
    @6
    @8
    @13
    @10
    cB
    ccup
    wbr
    #
    @15
    @4
    @16
    vx
    @10
    cA
    @9
    opex
    @2
    @10
    cB
    ccup
    breq1
    ceqsexv
    cA
    @9
    cB
    brsuccf.1
    cA
    snex
    #
    brsuccf.2
    brcup
    bitri
    @5
    @12
    vx
    @5
    @2
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
    cA
    @18
    cid
    wbr
    #
    cA
    @19
    csingle
    wbr
    #
    w3a
    #
    vb
    wex
    va
    wex
    #
    @4
    wa
    #
    @12
    @3
    @25
    @4
    va
    vb
    cA
    @2
    cid
    csingle
    brsuccf.1
    brtxp2
    anbi1i
    @24
    @4
    wa
    #
    vb
    wex
    va
    wex
    @18
    cA
    wceq
    #
    @19
    @9
    wceq
    #
    @21
    @4
    wa
    #
    w3a
    #
    vb
    wex
    va
    wex
    @26
    @12
    @27
    @31
    va
    vb
    @27
    @21
    @22
    @23
    wa
    #
    wa
    #
    @4
    wa
    @30
    @32
    wa
    #
    @31
    @24
    @33
    @4
    @21
    @22
    @23
    3anass
    anbi1i
    @21
    @32
    @4
    an32
    @32
    @30
    wa
    @28
    @29
    wa
    #
    @30
    wa
    @34
    @31
    @32
    @35
    @30
    @22
    @28
    @23
    @29
    @22
    cA
    @18
    wceq
    @28
    cA
    @18
    va
    vex
    ideq
    cA
    @18
    eqcom
    bitri
    cA
    @19
    brsuccf.1
    vb
    vex
    brsingle
    anbi12i
    anbi1i
    @30
    @32
    ancom
    @28
    @29
    @30
    df-3an
    3bitr4i
    3bitri
    2exbii
    @24
    @4
    va
    vb
    19.41vv
    @30
    @2
    cA
    @19
    cop
    #
    wceq
    #
    @4
    wa
    @12
    va
    vb
    cA
    @9
    brsuccf.1
    @17
    @28
    @21
    @37
    @4
    @28
    @20
    @36
    @2
    @18
    cA
    @19
    opeq1
    eqeq2d
    anbi1d
    @29
    @37
    @11
    @4
    @29
    @36
    @10
    @2
    @19
    @9
    cA
    opeq2
    eqeq2d
    anbi1d
    ceqsex2v
    3bitr3i
    bitri
    exbii
    @7
    @14
    cB
    cA
    df-suc
    eqeq2i
    3bitr4i
    3bitri
end
