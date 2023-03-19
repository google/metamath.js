include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "crab.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "cxp.mm"
include "wss.mm"
include "txtop.mm"
include "adantr.mm"
include "simprl.mm"
include "eqid.mm"
include "eltopss.mm"
include "syl2anc.mm"
include "wceq.mm"
include "txuni.mm"
include "sseqtr4d.mm"
include "imass1.mm"
include "syl.mm"
include "xpimasn.mm"
include "ad2antll.mm"
include "sseqtrd.mm"
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
include "ccn.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1t.mm"
include "cnima.mm"
include "eqeltrd.mm"

theorem imasnopn
  let cA: class A
  let cR: class R
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  assume imasnopn.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ K e. Top ) /\ ( R e. ( J tX K ) /\ A e. X ) ) -> ( R " { A } ) e. K )

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
    cJ
    cK
    ctx
    co
    #
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    wa
    #
    cR
    cA
    csn
    #
    cima
    #
    vy
    cK
    cuni
    #
    cA
    vy
    cv
    #
    cop
    #
    cmpt
    #
    ccnv
    cR
    cima
    #
    cK
    @7
    @9
    @12
    cR
    wcel
    #
    vy
    @10
    crab
    #
    @14
    @7
    vy
    @9
    @16
    @7
    vy
    nfv
    vy
    @9
    nfcv
    @15
    vy
    @10
    nfrab1
    @7
    @11
    @9
    wcel
    #
    @11
    @10
    wcel
    #
    @15
    wa
    #
    @11
    @16
    wcel
    @7
    @17
    @18
    @17
    wa
    @19
    @7
    @17
    @18
    @7
    @9
    @10
    @11
    @7
    @9
    cX
    @10
    cxp
    #
    @8
    cima
    #
    @10
    @7
    cR
    @20
    wss
    @9
    @21
    wss
    @7
    cR
    @3
    cuni
    #
    @20
    @7
    @3
    ctop
    wcel
    #
    @4
    cR
    @22
    wss
    @2
    @23
    @6
    cJ
    cK
    txtop
    adantr
    @2
    @4
    @5
    simprl
    #
    cR
    @3
    @22
    @22
    eqid
    eltopss
    syl2anc
    @2
    @20
    @22
    wceq
    @6
    cJ
    cK
    cX
    @10
    imasnopn.1
    @10
    eqid
    #
    txuni
    adantr
    sseqtr4d
    cR
    @20
    @8
    imass1
    syl
    @5
    @21
    @10
    wceq
    @2
    @4
    cX
    @10
    cA
    xpimasn
    ad2antll
    sseqtrd
    sseld
    pm4.71rd
    @7
    @17
    @15
    @18
    @5
    @17
    @15
    wb
    #
    @2
    @4
    @5
    @11
    cvv
    wcel
    @26
    vy
    vex
    cR
    cA
    @11
    cX
    cvv
    elimasng
    mpan2
    ad2antll
    anbi2d
    bitrd
    @15
    vy
    @10
    rabid
    syl6bbr
    eqrd
    vy
    @10
    @12
    cR
    @13
    @13
    eqid
    mptpreima
    syl6eqr
    @7
    @13
    cK
    @3
    ccn
    co
    wcel
    @4
    @14
    cK
    wcel
    @7
    vy
    cA
    @11
    cK
    cJ
    cK
    @10
    @1
    cK
    @10
    ctopon
    cfv
    wcel
    #
    @0
    @6
    @1
    @27
    cK
    @10
    @25
    toptopon
    biimpi
    ad2antlr
    #
    @7
    vy
    cA
    cK
    cJ
    @10
    cX
    @28
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
    @29
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
    @10
    @28
    cnmptid
    cnmpt1t
    @24
    cR
    @13
    cK
    @3
    cnima
    syl2anc
    eqeltrd
end
