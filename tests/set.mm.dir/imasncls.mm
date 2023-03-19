include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "ccl.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "csn.mm"
include "ccn.mm"
include "cuni.mm"
include "ctopon.mm"
include "toptopon.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1t.mm"
include "simprl.mm"
include "wceq.mm"
include "txuni.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cncls2i.mm"
include "syl2anc.mm"
include "crab.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "imass1.mm"
include "syl.mm"
include "xpimasn.mm"
include "ad2antll.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "cvv.mm"
include "vex.mm"
include "elimasng.mm"
include "mpan2.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "rabid.mm"
include "syl6bbr.mm"
include "eqrd.mm"
include "mptpreima.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "txtop.mm"
include "clsss3.mm"
include "sseqtr4d.mm"
include "3sstr4d.mm"

theorem imasncls
  let cA: class A
  let cR: class R
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume imasnopn.1: |- X = U. J
  assume imasnopn.2: |- Y = U. K


  assert |- ( ( ( J e. Top /\ K e. Top ) /\ ( R C_ ( X X. Y ) /\ A e. X ) ) -> ( ( cls ` K ) ` ( R " { A } ) ) C_ ( ( ( cls ` ( J tX K ) ) ` R ) " { A } ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cR
    cX
    cY
    cxp
    #
    wss
    #
    cA
    cX
    wcel
    #
    wa
    #
    wa
    #
    vy
    cY
    cA
    vy
    cv
    #
    cop
    #
    cmpt
    #
    ccnv
    #
    cR
    cima
    #
    cK
    ccl
    cfv
    #
    cfv
    #
    @11
    cR
    cJ
    cK
    ctx
    co
    #
    ccl
    cfv
    cfv
    #
    cima
    #
    cR
    cA
    csn
    #
    cima
    #
    @13
    cfv
    @16
    @18
    cima
    #
    @7
    @10
    cK
    @15
    ccn
    co
    wcel
    cR
    @15
    cuni
    #
    wss
    #
    @14
    @17
    wss
    @7
    vy
    cA
    @8
    cK
    cJ
    cK
    cY
    @1
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @0
    @6
    @1
    @23
    cK
    cY
    imasnopn.2
    toptopon
    biimpi
    ad2antlr
    #
    @7
    vy
    cA
    cK
    cJ
    cY
    cX
    @24
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    @6
    @0
    @25
    cJ
    cX
    imasnopn.1
    toptopon
    biimpi
    ad2antrr
    @2
    @4
    @5
    simprr
    cnmptc
    @7
    vy
    cK
    cY
    @24
    cnmptid
    cnmpt1t
    @7
    cR
    @3
    @21
    @2
    @4
    @5
    simprl
    #
    @2
    @3
    @21
    wceq
    @6
    cJ
    cK
    cX
    cY
    imasnopn.1
    imasnopn.2
    txuni
    adantr
    #
    sseqtrd
    #
    cR
    @10
    cK
    @15
    @21
    @21
    eqid
    #
    cncls2i
    syl2anc
    @7
    @19
    @12
    @13
    @7
    @19
    @9
    cR
    wcel
    #
    vy
    cY
    crab
    #
    @12
    @7
    vy
    @19
    @31
    @7
    vy
    nfv
    #
    vy
    @19
    nfcv
    @30
    vy
    cY
    nfrab1
    @7
    @8
    @19
    wcel
    #
    @8
    cY
    wcel
    #
    @30
    wa
    #
    @8
    @31
    wcel
    @7
    @33
    @34
    @33
    wa
    @35
    @7
    @33
    @34
    @7
    @19
    cY
    @8
    @7
    @19
    @3
    @18
    cima
    #
    cY
    @7
    @4
    @19
    @36
    wss
    @26
    cR
    @3
    @18
    imass1
    syl
    @5
    @36
    cY
    wceq
    @2
    @4
    cX
    cY
    cA
    xpimasn
    ad2antll
    #
    sseqtrd
    sseld
    pm4.71rd
    @7
    @33
    @30
    @34
    @5
    @33
    @30
    wb
    #
    @2
    @4
    @5
    @8
    cvv
    wcel
    #
    @38
    vy
    vex
    #
    cR
    cA
    @8
    cX
    cvv
    elimasng
    mpan2
    ad2antll
    anbi2d
    bitrd
    @30
    vy
    cY
    rabid
    syl6bbr
    eqrd
    vy
    cY
    @9
    cR
    @10
    @10
    eqid
    #
    mptpreima
    syl6eqr
    fveq2d
    @7
    @20
    @9
    @16
    wcel
    #
    vy
    cY
    crab
    #
    @17
    @7
    vy
    @20
    @43
    @32
    vy
    @20
    nfcv
    @42
    vy
    cY
    nfrab1
    @7
    @8
    @20
    wcel
    #
    @34
    @42
    wa
    #
    @8
    @43
    wcel
    @7
    @44
    @34
    @44
    wa
    @45
    @7
    @44
    @34
    @7
    @20
    cY
    @8
    @7
    @20
    @36
    cY
    @7
    @16
    @3
    wss
    @20
    @36
    wss
    @7
    @16
    @21
    @3
    @7
    @15
    ctop
    wcel
    #
    @22
    @16
    @21
    wss
    @2
    @46
    @6
    cJ
    cK
    txtop
    adantr
    @28
    cR
    @15
    @21
    @29
    clsss3
    syl2anc
    @27
    sseqtr4d
    @16
    @3
    @18
    imass1
    syl
    @37
    sseqtrd
    sseld
    pm4.71rd
    @7
    @44
    @42
    @34
    @5
    @44
    @42
    wb
    #
    @2
    @4
    @5
    @39
    @47
    @40
    @16
    cA
    @8
    cX
    cvv
    elimasng
    mpan2
    ad2antll
    anbi2d
    bitrd
    @42
    vy
    cY
    rabid
    syl6bbr
    eqrd
    vy
    cY
    @9
    @16
    @10
    @41
    mptpreima
    syl6eqr
    3sstr4d
end
