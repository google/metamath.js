include "cixp.mm"
include "ccl.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cmpt.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "cpw.mm"
include "wceq.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "elrab2.mm"
include "adantr.mm"
include "ineq1.mm"
include "wss.mm"
include "ssun1.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "imim2d.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ctop.mm"
include "cuni.mm"
include "wb.mm"
include "ctopon.mm"
include "crab.mm"
include "cvv.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "ssun2.mm"
include "uniexg.mm"
include "pwexg.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "snidg.mm"
include "syl.mm"
include "sseldi.mm"
include "epttop.mm"
include "syl2anc.mm"
include "topontop.mm"
include "toponuni.mm"
include "syl5sseq.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "elcls.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "mptelixpg.mm"
include "ne0i.mm"
include "pttopon.mm"
include "cls0.mm"
include "3netr4d.mm"
include "fveq2.mm"
include "necon3i.mm"

theorem dfac14lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cS: class S
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let vz: setvar z
  assume dfac14lem.i: |- ( ph -> I e. V )
  assume dfac14lem.s: |- ( ( ph /\ x e. I ) -> S e. W )
  assume dfac14lem.0: |- ( ( ph /\ x e. I ) -> S =/= (/) )
  assume dfac14lem.p: |- P = ~P U. S
  assume dfac14lem.r: |- R = { y e. ~P ( S u. { P } ) | ( P e. y -> y = ( S u. { P } ) ) }
  assume dfac14lem.j: |- J = ( Xt_ ` ( x e. I |-> R ) )
  assume dfac14lem.c: |- ( ph -> ( ( cls ` J ) ` X_ x e. I S ) = X_ x e. I ( ( cls ` R ) ` S ) )

  disjoint I x
  disjoint P y
  disjoint ph x
  disjoint S y
  disjoint x z
  disjoint I z
  disjoint y z
  disjoint P z
  disjoint ph z
  disjoint R z
  disjoint S z
  assert |- ( ph -> X_ x e. I S =/= (/) )

  proof
    wph
    vx
    cI
    cS
    cixp
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    c0
    @1
    cfv
    #
    wne
    @0
    c0
    wne
    wph
    vx
    cI
    cS
    cR
    ccl
    cfv
    cfv
    #
    cixp
    #
    c0
    @2
    @3
    wph
    vx
    cI
    cP
    cmpt
    #
    @5
    wcel
    #
    @5
    c0
    wne
    wph
    @7
    cP
    @4
    wcel
    #
    vx
    cI
    wral
    #
    wph
    @8
    vx
    cI
    wph
    vx
    cv
    cI
    wcel
    wa
    #
    @8
    cP
    vz
    cv
    #
    wcel
    #
    @11
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vz
    cR
    wral
    #
    @10
    @15
    vz
    cR
    @11
    cR
    wcel
    @11
    cS
    cP
    csn
    #
    cun
    #
    cpw
    #
    wcel
    #
    @12
    @11
    @18
    wceq
    #
    wi
    #
    wa
    @10
    @15
    cP
    vy
    cv
    #
    wcel
    #
    @23
    @18
    wceq
    #
    wi
    #
    @22
    vy
    @11
    @19
    cR
    @23
    @11
    wceq
    @24
    @12
    @25
    @21
    @23
    @11
    cP
    eleq2
    @23
    @11
    @18
    eqeq1
    imbi12d
    dfac14lem.r
    elrab2
    @10
    @20
    @22
    @15
    @10
    @20
    wa
    #
    @21
    @14
    @12
    @27
    @14
    @21
    cS
    c0
    wne
    #
    @10
    @28
    @20
    dfac14lem.0
    adantr
    @21
    @13
    cS
    c0
    @21
    @13
    @18
    cS
    cin
    #
    cS
    @11
    @18
    cS
    ineq1
    cS
    @18
    wss
    @29
    cS
    wceq
    cS
    @17
    ssun1
    #
    cS
    @18
    sseqin2
    mpbi
    syl6eq
    neeq1d
    syl5ibrcom
    imim2d
    expimpd
    syl5bi
    ralrimiv
    @10
    cR
    ctop
    wcel
    #
    cS
    cR
    cuni
    #
    wss
    cP
    @32
    wcel
    @8
    @16
    wb
    @10
    cR
    @18
    ctopon
    cfv
    #
    wcel
    #
    @31
    @10
    cR
    @26
    vy
    @19
    crab
    #
    @33
    dfac14lem.r
    @10
    @18
    cvv
    wcel
    #
    cP
    @18
    wcel
    @35
    @33
    wcel
    @10
    cS
    cW
    wcel
    #
    @17
    cvv
    wcel
    @36
    dfac14lem.s
    cP
    snex
    cS
    @17
    cW
    cvv
    unexg
    sylancl
    @10
    @17
    @18
    cP
    @17
    cS
    ssun2
    @10
    cP
    cvv
    wcel
    cP
    @17
    wcel
    @10
    cP
    cS
    cuni
    #
    cpw
    #
    cvv
    dfac14lem.p
    @10
    @37
    @38
    cvv
    wcel
    @39
    cvv
    wcel
    dfac14lem.s
    cS
    cW
    uniexg
    @38
    cvv
    pwexg
    3syl
    syl5eqel
    cP
    cvv
    snidg
    syl
    sseldi
    #
    vy
    @18
    cP
    cvv
    epttop
    syl2anc
    syl5eqel
    #
    @18
    cR
    topontop
    syl
    @10
    @18
    cS
    @32
    @30
    @10
    @34
    @18
    @32
    wceq
    @41
    @18
    cR
    toponuni
    syl
    #
    syl5sseq
    @10
    cP
    @18
    @32
    @40
    @42
    eleqtrd
    vz
    cP
    cS
    cR
    @32
    @32
    eqid
    elcls
    syl3anc
    mpbird
    ralrimiva
    wph
    cI
    cV
    wcel
    #
    @7
    @9
    wb
    dfac14lem.i
    vx
    cI
    cP
    @4
    cV
    mptelixpg
    syl
    mpbird
    @5
    @6
    ne0i
    syl
    dfac14lem.c
    wph
    cJ
    vx
    cI
    @18
    cixp
    #
    ctopon
    cfv
    wcel
    #
    cJ
    ctop
    wcel
    @3
    c0
    wceq
    wph
    @43
    @34
    vx
    cI
    wral
    @45
    dfac14lem.i
    wph
    @34
    vx
    cI
    @41
    ralrimiva
    vx
    cI
    @18
    cJ
    cR
    cV
    dfac14lem.j
    pttopon
    syl2anc
    @44
    cJ
    topontop
    cJ
    cls0
    3syl
    3netr4d
    @0
    c0
    @2
    @3
    @0
    c0
    @1
    fveq2
    necon3i
    syl
end
