include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cordt.mm"
include "cfv.mm"
include "cfi.mm"
include "ctg.mm"
include "cvv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "eqid.mm"
include "ordtuni.mm"
include "adantr.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "ssfii.mm"
include "syl.mm"
include "ctb.mm"
include "fibas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "syl6ss.mm"
include "ordtval.mm"
include "sseqtr4d.mm"
include "ssun2.mm"
include "ssun1.mm"
include "wrex.mm"
include "simpr.mm"
include "eqidd.mm"
include "breq2.mm"
include "notbid.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "rabexg.mm"
include "elrnmpt.mm"
include "3syl.mm"
include "mpbird.mm"
include "sseldi.mm"
include "sseldd.mm"

theorem ordtopn1
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cV: class V
  let cX: class X
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume ordttopon.3: |- X = dom R

  disjoint P x
  disjoint R x
  disjoint V x
  disjoint X x
  disjoint A x
  disjoint B x
  disjoint x y
  disjoint P y
  disjoint R y
  disjoint V y
  disjoint X y
  assert |- ( ( R e. V /\ P e. X ) -> { x e. X | -. x R P } e. ( ordTop ` R ) )

  proof
    cR
    cV
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cX
    csn
    #
    vy
    cX
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vx
    cX
    crab
    #
    cmpt
    #
    crn
    #
    vy
    cX
    @5
    @4
    cR
    wbr
    wn
    vx
    cX
    crab
    cmpt
    crn
    #
    cun
    #
    cun
    #
    cR
    cordt
    cfv
    #
    @4
    cP
    cR
    wbr
    #
    wn
    #
    vx
    cX
    crab
    #
    @2
    @13
    @13
    cfi
    cfv
    #
    ctg
    cfv
    #
    @14
    @2
    @13
    @18
    @19
    @2
    @13
    cvv
    wcel
    #
    @13
    @18
    wss
    @2
    @13
    cuni
    #
    cvv
    wcel
    @20
    @2
    cX
    @21
    cvv
    @0
    cX
    @21
    wceq
    @1
    vy
    vx
    @10
    @11
    cR
    cV
    cX
    ordttopon.3
    @10
    eqid
    #
    @11
    eqid
    #
    ordtuni
    adantr
    @0
    cX
    cvv
    wcel
    #
    @1
    @0
    cX
    cR
    cdm
    cvv
    ordttopon.3
    cR
    cV
    dmexg
    syl5eqel
    adantr
    #
    eqeltrrd
    @13
    uniexb
    sylibr
    @13
    cvv
    ssfii
    syl
    @18
    ctb
    wcel
    @18
    @19
    wss
    @13
    fibas
    @18
    ctb
    bastg
    ax-mp
    syl6ss
    @0
    @14
    @19
    wceq
    @1
    vy
    vx
    @10
    @11
    cR
    cV
    cX
    ordttopon.3
    @22
    @23
    ordtval
    adantr
    sseqtr4d
    @2
    @12
    @13
    @17
    @12
    @3
    ssun2
    @2
    @10
    @12
    @17
    @10
    @11
    ssun1
    @2
    @17
    @10
    wcel
    #
    @17
    @8
    wceq
    #
    vy
    cX
    wrex
    #
    @2
    @1
    @17
    @17
    wceq
    #
    @28
    @0
    @1
    simpr
    @2
    @17
    eqidd
    @27
    @29
    vy
    cP
    cX
    @5
    cP
    wceq
    #
    @8
    @17
    @17
    @30
    @7
    @16
    vx
    cX
    @30
    @6
    @15
    @5
    cP
    @4
    cR
    breq2
    notbid
    rabbidv
    eqeq2d
    rspcev
    syl2anc
    @2
    @24
    @17
    cvv
    wcel
    @26
    @28
    wb
    @25
    @16
    vx
    cX
    cvv
    rabexg
    vy
    cX
    @8
    @17
    @9
    cvv
    @9
    eqid
    elrnmpt
    3syl
    mpbird
    sseldi
    sseldi
    sseldd
end
