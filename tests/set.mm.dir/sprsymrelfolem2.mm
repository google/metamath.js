include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "w3a.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cspr.mm"
include "cfv.mm"
include "wi.mm"
include "cop.mm"
include "df-br.mm"
include "simpl.mm"
include "ssel.mm"
include "adantl.mm"
include "imp.mm"
include "opelxp.mm"
include "sylib.mm"
include "prelspr.mm"
include "syl2an2r.mm"
include "ex.mm"
include "syl5bi.mm"
include "3adant3.mm"
include "weq.mm"
include "wo.mm"
include "vex.mm"
include "preq12b.mm"
include "breq12.mm"
include "biimpd.mm"
include "com12.mm"
include "adantr.mm"
include "rsp2.mm"
include "ancomsd.mm"
include "3ad2ant3.mm"
include "com23.mm"
include "eleq1.mm"
include "bi2anan9r.mm"
include "ancoms.mm"
include "imbi12d.mm"
include "mpbid.mm"
include "expimpd.mm"
include "jaoi.mm"
include "ralrimivva.mm"
include "crab.mm"
include "eleq2i.mm"
include "eqeq1.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "eqidd.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cvv.mm"
include "prsprel.mm"
include "mpanr12.mm"
include "syl6bi.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "breq1.mm"
include "preq2.mm"
include "breq2.mm"
include "rspc2v.mm"
include "a1d.mm"
include "imp4c.mm"
include "mpcom.mm"
include "sylanb.mm"
include "rexlimiva.mm"
include "impbid.mm"

theorem sprsymrelfolem2
  let vx: setvar x
  let vy: setvar y
  let cQ: class Q
  let cR: class R
  let cV: class V
  let cW: class W
  let vq: setvar q
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume sprsymrelfo.q: |- Q = { q e. ( Pairs ` V ) | A. a e. V A. b e. V ( q = { a , b } -> a R b ) }

  disjoint V q
  disjoint Q c
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R q
  disjoint R x
  disjoint R y
  disjoint a b
  disjoint a c
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint c q
  disjoint c x
  disjoint c y
  disjoint q x
  disjoint q y
  disjoint x y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint k x
  assert |- ( ( V e. W /\ R C_ ( V X. V ) /\ A. x e. V A. y e. V ( x R y <-> y R x ) ) -> ( x R y <-> E. c e. Q c = { x , y } ) )

  proof
    cV
    cW
    wcel
    #
    cR
    cV
    cV
    cxp
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @4
    @3
    cR
    wbr
    #
    wb
    #
    vy
    cV
    wral
    vx
    cV
    wral
    #
    w3a
    #
    @5
    vc
    cv
    #
    @3
    @4
    cpr
    #
    wceq
    #
    vc
    cQ
    wrex
    #
    @9
    @5
    @13
    @9
    @5
    wa
    #
    @11
    cQ
    wcel
    #
    @11
    @11
    wceq
    #
    @13
    @14
    @11
    cV
    cspr
    cfv
    #
    wcel
    #
    @11
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    @19
    @20
    cR
    wbr
    #
    wi
    #
    vb
    cV
    wral
    va
    cV
    wral
    #
    @15
    @9
    @5
    @18
    @0
    @2
    @5
    @18
    wi
    @8
    @5
    @3
    @4
    cop
    #
    cR
    wcel
    #
    @0
    @2
    wa
    #
    @18
    @3
    @4
    cR
    df-br
    @28
    @27
    @18
    @28
    @0
    @27
    @3
    cV
    wcel
    #
    @4
    cV
    wcel
    #
    wa
    #
    @18
    @0
    @2
    simpl
    @28
    @27
    wa
    @26
    @1
    wcel
    #
    @31
    @28
    @27
    @32
    @2
    @27
    @32
    wi
    @0
    cR
    @1
    @26
    ssel
    adantl
    imp
    @3
    @4
    cV
    cV
    opelxp
    sylib
    cV
    cW
    @3
    @4
    prelspr
    syl2an2r
    ex
    syl5bi
    3adant3
    imp
    @14
    @24
    va
    vb
    cV
    cV
    @22
    vx
    va
    weq
    vy
    vb
    weq
    wa
    #
    vx
    vb
    weq
    #
    vy
    va
    weq
    #
    wa
    #
    wo
    #
    @14
    @19
    cV
    wcel
    #
    @20
    cV
    wcel
    #
    wa
    #
    wa
    #
    @23
    @3
    @4
    @19
    @20
    vx
    vex
    #
    vy
    vex
    #
    va
    vex
    vb
    vex
    preq12b
    @37
    @41
    @23
    @33
    @41
    @23
    wi
    @36
    @41
    @33
    @23
    @14
    @33
    @23
    wi
    #
    @40
    @5
    @44
    @9
    @33
    @5
    @23
    @33
    @5
    @23
    @3
    @19
    @4
    @20
    cR
    breq12
    biimpd
    com12
    adantl
    adantr
    com12
    @36
    @14
    @40
    @23
    @36
    @14
    wa
    @30
    @29
    wa
    #
    @6
    wi
    #
    @40
    @23
    wi
    #
    @14
    @46
    @36
    @9
    @5
    @46
    @9
    @45
    @5
    @6
    @8
    @0
    @45
    @5
    @6
    wi
    #
    wi
    @2
    @8
    @45
    @48
    @8
    @45
    wa
    @5
    @6
    @8
    @45
    @7
    @8
    @29
    @30
    @7
    @7
    vx
    vy
    cV
    cV
    rsp2
    ancomsd
    imp
    biimpd
    ex
    3ad2ant3
    com23
    imp
    adantl
    @36
    @46
    @47
    wb
    @14
    @36
    @45
    @40
    @6
    @23
    @35
    @30
    @38
    @34
    @29
    @39
    @4
    @19
    cV
    eleq1
    @3
    @20
    cV
    eleq1
    bi2anan9r
    @35
    @34
    @6
    @23
    wb
    @4
    @19
    @3
    @20
    cR
    breq12
    ancoms
    imbi12d
    adantr
    mpbid
    expimpd
    jaoi
    com12
    syl5bi
    ralrimivva
    @15
    @11
    vq
    cv
    #
    @21
    wceq
    #
    @23
    wi
    #
    vb
    cV
    wral
    va
    cV
    wral
    #
    vq
    @17
    crab
    #
    wcel
    @18
    @25
    wa
    cQ
    @53
    @11
    sprsymrelfo.q
    eleq2i
    @52
    @25
    vq
    @11
    @17
    @49
    @11
    wceq
    #
    @51
    @24
    va
    vb
    cV
    cV
    @54
    @50
    @22
    @23
    @49
    @11
    @21
    eqeq1
    imbi1d
    2ralbidv
    elrab
    bitri
    sylanbrc
    @14
    @11
    eqidd
    @12
    @16
    vc
    @11
    cQ
    @10
    @11
    @11
    eqeq1
    rspcev
    syl2anc
    ex
    @13
    @9
    @5
    @12
    @9
    @5
    wi
    #
    vc
    cQ
    @10
    cQ
    wcel
    #
    @10
    @17
    wcel
    #
    @10
    @21
    wceq
    #
    @23
    wi
    #
    vb
    cV
    wral
    va
    cV
    wral
    #
    wa
    #
    @12
    @55
    @56
    @10
    @53
    wcel
    @61
    cQ
    @53
    @10
    sprsymrelfo.q
    eleq2i
    @52
    @60
    vq
    @10
    @17
    vq
    vc
    weq
    #
    @51
    @59
    va
    vb
    cV
    cV
    @62
    @50
    @58
    @23
    @49
    @10
    @21
    eqeq1
    imbi1d
    2ralbidv
    elrab
    bitri
    @61
    @12
    wa
    #
    @5
    @9
    @31
    @63
    @5
    @61
    @12
    @31
    @57
    @12
    @31
    wi
    @60
    @12
    @57
    @31
    @12
    @57
    @18
    @31
    @10
    @11
    @17
    eleq1
    @18
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @31
    @42
    @43
    cvv
    cV
    cvv
    @3
    @4
    prsprel
    mpanr12
    syl6bi
    com12
    adantr
    imp
    @31
    @57
    @60
    @12
    @5
    @31
    @60
    @12
    @5
    wi
    #
    wi
    @57
    @59
    @64
    @10
    @3
    @20
    cpr
    #
    wceq
    #
    @3
    @20
    cR
    wbr
    #
    wi
    va
    vb
    @3
    @4
    cV
    cV
    va
    vx
    weq
    #
    @58
    @66
    @23
    @67
    @68
    @21
    @65
    @10
    @19
    @3
    @20
    preq1
    eqeq2d
    @19
    @3
    @20
    cR
    breq1
    imbi12d
    vb
    vy
    weq
    #
    @66
    @12
    @67
    @5
    @69
    @65
    @11
    @10
    @20
    @4
    @3
    preq2
    eqeq2d
    @20
    @4
    @3
    cR
    breq2
    imbi12d
    rspc2v
    a1d
    imp4c
    mpcom
    a1d
    sylanb
    rexlimiva
    com12
    impbid
end
