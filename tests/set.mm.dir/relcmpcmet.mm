include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccfil.mm"
include "wral.mm"
include "cms.mm"
include "wa.mm"
include "cbl.mm"
include "cxmt.mm"
include "crp.mm"
include "wrex.mm"
include "metxmet.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "cfil3i.mm"
include "syl3anc.mm"
include "ccl.mm"
include "crest.mm"
include "cfcls.mm"
include "wss.mm"
include "cin.mm"
include "ctopon.mm"
include "cfil.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "mopntopon.mm"
include "cfilfil.mm"
include "sylan.mm"
include "simprr.mm"
include "cuni.mm"
include "ctop.mm"
include "topontop.mm"
include "cxr.mm"
include "simprl.mm"
include "rpxrd.mm"
include "blssm.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "sscls.mm"
include "filss.mm"
include "syl13anc.mm"
include "fclsrest.mm"
include "inss1.mm"
include "cdm.mm"
include "cfilfcls.mm"
include "ad2antlr.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "ccmp.mm"
include "ad2ant2r.mm"
include "cdif.mm"
include "wn.mm"
include "cfbas.mm"
include "filfbas.mm"
include "fbncp.mm"
include "wb.mm"
include "trfil3.mm"
include "mpbird.mm"
include "resttopon.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "fclscmpi.mm"
include "ssn0.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "iscmet.mm"
include "sylanbrc.mm"

theorem relcmpcmet
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cR: class R
  let cJ: class J
  let cX: class X
  let vf: setvar f
  assume relcmpcmet.1: |- J = ( MetOpen ` D )
  assume relcmpcmet.2: |- ( ph -> D e. ( Met ` X ) )
  assume relcmpcmet.3: |- ( ph -> R e. RR+ )
  assume relcmpcmet.4: |- ( ( ph /\ x e. X ) -> ( J |`t ( ( cls ` J ) ` ( x ( ball ` D ) R ) ) ) e. Comp )

  disjoint D x
  disjoint J x
  disjoint ph x
  disjoint R x
  disjoint X x
  disjoint f x
  disjoint D f
  disjoint J f
  disjoint f ph
  disjoint X f
  assert |- ( ph -> D e. ( CMet ` X ) )

  proof
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cJ
    vf
    cv
    #
    cflim
    co
    #
    c0
    wne
    #
    vf
    cD
    ccfil
    cfv
    #
    wral
    cD
    cX
    cms
    cfv
    wcel
    relcmpcmet.2
    wph
    @3
    vf
    @4
    wph
    @1
    @4
    wcel
    #
    wa
    #
    vx
    cv
    #
    cR
    cD
    cbl
    cfv
    co
    #
    @1
    wcel
    #
    @3
    vx
    cX
    @6
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @5
    cR
    crp
    wcel
    #
    @9
    vx
    cX
    wrex
    wph
    @10
    @5
    wph
    @0
    @10
    relcmpcmet.2
    cD
    cX
    metxmet
    syl
    #
    adantr
    wph
    @5
    simpr
    wph
    @11
    @5
    relcmpcmet.3
    adantr
    vx
    cD
    cR
    @1
    cX
    cfil3i
    syl3anc
    @6
    @7
    cX
    wcel
    #
    @9
    wa
    #
    wa
    #
    cJ
    @8
    cJ
    ccl
    cfv
    cfv
    #
    crest
    co
    #
    @1
    @16
    crest
    co
    #
    cfcls
    co
    #
    @2
    wss
    @19
    c0
    wne
    #
    @3
    @15
    @19
    cJ
    @1
    cfcls
    co
    #
    @16
    cin
    #
    @2
    @15
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    cX
    cfil
    cfv
    wcel
    #
    @16
    @1
    wcel
    #
    @19
    @22
    wceq
    @15
    @10
    @23
    wph
    @10
    @5
    @14
    @12
    ad2antrr
    #
    cD
    cJ
    cX
    relcmpcmet.1
    mopntopon
    syl
    #
    @6
    @24
    @14
    wph
    @10
    @5
    @24
    @12
    cD
    @1
    cX
    cfilfil
    sylan
    adantr
    #
    @15
    @24
    @9
    @16
    cX
    wss
    #
    @8
    @16
    wss
    #
    @25
    @28
    @6
    @13
    @9
    simprr
    @15
    @16
    cJ
    cuni
    #
    cX
    @15
    cJ
    ctop
    wcel
    #
    @8
    @31
    wss
    #
    @16
    @31
    wss
    @15
    @23
    @32
    @27
    cX
    cJ
    topontop
    syl
    #
    @15
    @8
    cX
    @31
    @15
    @10
    @13
    cR
    cxr
    wcel
    #
    @8
    cX
    wss
    @26
    @6
    @13
    @9
    simprl
    wph
    @35
    @5
    @14
    wph
    cR
    relcmpcmet.3
    rpxrd
    ad2antrr
    cD
    @7
    cR
    cX
    blssm
    syl3anc
    @15
    @23
    cX
    @31
    wceq
    @27
    cX
    cJ
    toponuni
    syl
    #
    sseqtrd
    #
    @8
    cJ
    @31
    @31
    eqid
    #
    clsss3
    syl2anc
    @36
    sseqtr4d
    #
    @15
    @32
    @33
    @30
    @34
    @37
    @8
    cJ
    @31
    @38
    sscls
    syl2anc
    @8
    @16
    @1
    cX
    filss
    syl13anc
    #
    @1
    cJ
    cX
    @16
    fclsrest
    syl3anc
    @15
    @21
    @22
    @2
    @21
    @16
    inss1
    @5
    @21
    @2
    wceq
    wph
    @14
    cD
    @1
    cJ
    cD
    cdm
    cdm
    #
    relcmpcmet.1
    @41
    eqid
    cfilfcls
    ad2antlr
    syl5sseq
    eqsstrd
    @15
    @17
    ccmp
    wcel
    #
    @18
    @17
    cuni
    #
    cfil
    cfv
    #
    wcel
    @20
    wph
    @13
    @42
    @5
    @9
    relcmpcmet.4
    ad2ant2r
    @15
    @18
    @16
    cfil
    cfv
    #
    @44
    @15
    @18
    @45
    wcel
    #
    cX
    @16
    cdif
    @1
    wcel
    wn
    #
    @15
    @1
    cX
    cfbas
    cfv
    wcel
    #
    @25
    @47
    @15
    @24
    @48
    @28
    @1
    cX
    filfbas
    syl
    @40
    @16
    cX
    @1
    cX
    fbncp
    syl2anc
    @15
    @24
    @29
    @46
    @47
    wb
    @28
    @39
    @16
    @1
    cX
    trfil3
    syl2anc
    mpbird
    @15
    @16
    @43
    cfil
    @15
    @17
    @16
    ctopon
    cfv
    wcel
    #
    @16
    @43
    wceq
    @15
    @23
    @29
    @49
    @27
    @39
    @16
    cJ
    cX
    resttopon
    syl2anc
    @16
    @17
    toponuni
    syl
    fveq2d
    eleqtrd
    @18
    @17
    @43
    @43
    eqid
    fclscmpi
    syl2anc
    @19
    @2
    ssn0
    syl2anc
    rexlimddv
    ralrimiva
    cD
    vf
    cJ
    cX
    relcmpcmet.1
    iscmet
    sylanbrc
end
