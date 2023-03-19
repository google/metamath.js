include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "cmpt.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "crab.mm"
include "ctop.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "ctopon.mm"
include "ppttop.mm"
include "topontop.mm"
include "syl.mm"
include "wf.mm"
include "simpr.mm"
include "simplr.mm"
include "prssi.mm"
include "syl2anc.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "prid2g.mm"
include "ad2antlr.mm"
include "orcd.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "sselda.mm"
include "prid1g.mm"
include "adantl.mm"
include "wn.mm"
include "n0i.mm"
include "simplrr.mm"
include "ord.mm"
include "mt3d.mm"
include "preq1.mm"
include "eleq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "cvv.mm"
include "wb.mm"
include "rgenw.mm"
include "sseq1.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "ralrimiva.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "basgen2.mm"
include "syl3anc.mm"
include "cbvrabv.mm"
include "syl6req.mm"

theorem pptbas
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint P x
  disjoint V x
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint P v
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint V w
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ P e. A ) -> { x e. ~P A | ( P e. x \/ x = (/) ) } = ( topGen ` ran ( x e. A |-> { x , P } ) ) )

  proof
    cA
    cV
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    vx
    cA
    vx
    cv
    #
    cP
    cpr
    #
    cmpt
    #
    crn
    #
    ctg
    cfv
    #
    cP
    vy
    cv
    #
    wcel
    #
    @8
    c0
    wceq
    #
    wo
    #
    vy
    cA
    cpw
    #
    crab
    #
    cP
    @3
    wcel
    #
    @3
    c0
    wceq
    #
    wo
    #
    vx
    @12
    crab
    @2
    @13
    ctop
    wcel
    #
    @6
    @13
    wss
    #
    vw
    cv
    #
    vv
    cv
    #
    wcel
    #
    @20
    vz
    cv
    #
    wss
    #
    wa
    #
    vv
    @6
    wrex
    #
    vw
    @22
    wral
    #
    vz
    @13
    wral
    @7
    @13
    wceq
    @2
    @13
    cA
    ctopon
    cfv
    wcel
    @17
    vy
    cA
    cP
    cV
    ppttop
    cA
    @13
    topontop
    syl
    @2
    cA
    @13
    @5
    wf
    @18
    @2
    vx
    cA
    @4
    @13
    @5
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @4
    @12
    wcel
    #
    cP
    @4
    wcel
    #
    @4
    c0
    wceq
    #
    wo
    #
    @4
    @13
    wcel
    @28
    @4
    cA
    wss
    #
    @29
    @28
    @27
    @1
    @33
    @2
    @27
    simpr
    @0
    @1
    @27
    simplr
    @3
    cP
    cA
    prssi
    syl2anc
    @4
    cA
    @3
    cP
    prex
    #
    elpw
    sylibr
    @28
    @30
    @31
    @1
    @30
    @0
    @27
    @3
    cP
    cA
    prid2g
    ad2antlr
    orcd
    @11
    @32
    vy
    @4
    @12
    @8
    @4
    wceq
    @9
    @30
    @10
    @31
    @8
    @4
    cP
    eleq2
    @8
    @4
    c0
    eqeq1
    orbi12d
    elrab
    sylanbrc
    @5
    eqid
    #
    fmptd
    cA
    @13
    @5
    frn
    syl
    @2
    @26
    vz
    @13
    @22
    @13
    wcel
    @22
    @12
    wcel
    #
    cP
    @22
    wcel
    #
    @22
    c0
    wceq
    #
    wo
    #
    wa
    #
    @2
    @26
    @11
    @39
    vy
    @22
    @12
    @8
    @22
    wceq
    @9
    @37
    @10
    @38
    @8
    @22
    cP
    eleq2
    @8
    @22
    c0
    eqeq1
    orbi12d
    elrab
    @2
    @40
    @26
    @2
    @40
    wa
    #
    @25
    vw
    @22
    @41
    @19
    @22
    wcel
    #
    wa
    #
    @19
    @4
    wcel
    #
    @4
    @22
    wss
    #
    wa
    #
    vx
    cA
    wrex
    #
    @25
    @43
    @19
    cA
    wcel
    @19
    @19
    cP
    cpr
    #
    wcel
    #
    @48
    @22
    wss
    #
    @47
    @41
    @22
    cA
    @19
    @36
    @22
    cA
    wss
    @2
    @39
    @22
    cA
    elpwi
    ad2antrl
    sselda
    @42
    @49
    @41
    @19
    cP
    @22
    prid1g
    adantl
    @43
    @42
    @37
    @50
    @41
    @42
    simpr
    @43
    @37
    @38
    @42
    @38
    wn
    @41
    @22
    @19
    n0i
    adantl
    @43
    @37
    @38
    @2
    @36
    @39
    @42
    simplrr
    ord
    mt3d
    @19
    cP
    @22
    prssi
    syl2anc
    @46
    @49
    @50
    wa
    vx
    @19
    cA
    @3
    @19
    wceq
    #
    @44
    @49
    @45
    @50
    @51
    @4
    @48
    @19
    @3
    @19
    cP
    preq1
    #
    eleq2d
    @51
    @4
    @48
    @22
    @52
    sseq1d
    anbi12d
    rspcev
    syl12anc
    @4
    cvv
    wcel
    #
    vx
    cA
    wral
    @25
    @47
    wb
    @53
    vx
    cA
    @34
    rgenw
    @24
    @46
    vx
    vv
    cA
    @4
    @5
    cvv
    @35
    @20
    @4
    wceq
    @21
    @44
    @23
    @45
    @20
    @4
    @19
    eleq2
    @20
    @4
    @22
    sseq1
    anbi12d
    rexrnmpt
    ax-mp
    sylibr
    ralrimiva
    ex
    syl5bi
    ralrimiv
    vz
    vw
    vv
    @6
    @13
    basgen2
    syl3anc
    @11
    @16
    vy
    vx
    @12
    @8
    @3
    wceq
    @9
    @14
    @10
    @15
    @8
    @3
    cP
    eleq2
    @8
    @3
    c0
    eqeq1
    orbi12d
    cbvrabv
    syl6req
end
