include "cioo.mm"
include "co.mm"
include "cres.mm"
include "climc.mm"
include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "iooss1.mm"
include "syl2anc.mm"
include "resabs1d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cin.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "crest.mm"
include "cc.mm"
include "wf.mm"
include "fresin.mm"
include "syl.mm"
include "ssind.mm"
include "inss2.mm"
include "ioosscn.mm"
include "sstri.mm"
include "a1i.mm"
include "eqid.mm"
include "cioc.mm"
include "cnt.mm"
include "clt.mm"
include "rexrd.mm"
include "ubioc1.mm"
include "syl3anc.mm"
include "wceq.mm"
include "snunioo2.mm"
include "fveq2d.mm"
include "ctop.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "ovex.mm"
include "inex2.mm"
include "snex.mm"
include "unex.mm"
include "resttop.mm"
include "mp2an.mm"
include "crn.mm"
include "ctg.mm"
include "cpnf.mm"
include "cv.mm"
include "pnfxr.mm"
include "xrleid.mm"
include "ltpnfd.mm"
include "iocssioo.mm"
include "syl22anc.mm"
include "wral.mm"
include "wa.mm"
include "simpr.mm"
include "cr.mm"
include "snidg.mm"
include "elun2.mm"
include "3syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "simpll.mm"
include "iocssre.mm"
include "sselda.mm"
include "iocgtlb.mm"
include "ad2antrr.mm"
include "iocleub.mm"
include "wne.mm"
include "neqne.mm"
include "adantl.mm"
include "necomd.mm"
include "leneltd.mm"
include "eliood.mm"
include "elun1.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "sseld.mm"
include "ioossioc.mm"
include "elinel1.mm"
include "elioored.mm"
include "ad2antlr.mm"
include "ioogtlb.mm"
include "elinel2.mm"
include "id.mm"
include "velsn.mm"
include "sylnibr.mm"
include "elunnel2.mm"
include "syl2an.mm"
include "sseldi.mm"
include "adantll.mm"
include "iooltub.mm"
include "ex.mm"
include "impbid.mm"
include "eqrdv.mm"
include "retop.mm"
include "iooretop.mm"
include "elrestr.mm"
include "tgioo2.mm"
include "oveq1i.mm"
include "ioossre.mm"
include "snssd.mm"
include "unssd.mm"
include "reex.mm"
include "restabs.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "isopn3i.mm"
include "eqtr2d.mm"
include "limcres.mm"
include "eqtrd.mm"

theorem limcresiooub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vx: setvar x
  assume limcresiooub.f: |- ( ph -> F : A --> CC )
  assume limcresiooub.b: |- ( ph -> B e. RR* )
  assume limcresiooub.c: |- ( ph -> C e. RR )
  assume limcresiooub.bltc: |- ( ph -> B < C )
  assume limcresiooub.bcss: |- ( ph -> ( B (,) C ) C_ A )
  assume limcresiooub.d: |- ( ph -> D e. RR* )
  assume limcresiooub.cled: |- ( ph -> D <_ B )


  assert |- ( ph -> ( ( F |` ( B (,) C ) ) limCC C ) = ( ( F |` ( D (,) C ) ) limCC C ) )

  proof
    wph
    cF
    cB
    cC
    cioo
    co
    #
    cres
    #
    cC
    climc
    co
    cF
    cD
    cC
    cioo
    co
    #
    cres
    #
    @0
    cres
    #
    cC
    climc
    co
    @3
    cC
    climc
    co
    wph
    @1
    @4
    cC
    climc
    wph
    @4
    @1
    wph
    cF
    @0
    @2
    wph
    cD
    cxr
    wcel
    #
    cD
    cB
    cle
    wbr
    @0
    @2
    wss
    limcresiooub.d
    limcresiooub.cled
    cD
    cB
    cC
    iooss1
    syl2anc
    #
    resabs1d
    eqcomd
    oveq1d
    wph
    cA
    @2
    cin
    #
    cC
    @0
    @3
    ccnfld
    ctopn
    cfv
    #
    @7
    cC
    csn
    #
    cun
    #
    crest
    co
    #
    @8
    wph
    cA
    cc
    cF
    wf
    @7
    cc
    @3
    wf
    limcresiooub.f
    cA
    cc
    cF
    @2
    fresin
    syl
    wph
    @0
    cA
    @2
    limcresiooub.bcss
    @6
    ssind
    #
    @7
    cc
    wss
    wph
    @7
    @2
    cc
    cA
    @2
    inss2
    #
    cD
    cC
    ioosscn
    sstri
    a1i
    @8
    eqid
    #
    @11
    eqid
    wph
    cC
    cB
    cC
    cioc
    co
    #
    @0
    @9
    cun
    #
    @11
    cnt
    cfv
    #
    cfv
    #
    wph
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    cB
    cC
    clt
    wbr
    #
    cC
    @15
    wcel
    #
    limcresiooub.b
    wph
    cC
    limcresiooub.c
    rexrd
    #
    limcresiooub.bltc
    cB
    cC
    ubioc1
    syl3anc
    #
    wph
    @18
    @15
    @17
    cfv
    #
    @15
    wph
    @16
    @15
    @17
    wph
    @19
    @20
    @21
    @16
    @15
    wceq
    limcresiooub.b
    @23
    limcresiooub.bltc
    cB
    cC
    snunioo2
    syl3anc
    fveq2d
    wph
    @11
    ctop
    wcel
    #
    @15
    @11
    wcel
    @25
    @15
    wceq
    @26
    wph
    @8
    ctop
    wcel
    #
    @10
    cvv
    wcel
    #
    @26
    @8
    @14
    cnfldtop
    #
    @7
    @9
    @2
    cA
    cD
    cC
    cioo
    ovex
    inex2
    cC
    snex
    unex
    #
    @10
    @8
    cvv
    resttop
    mp2an
    a1i
    wph
    @15
    cioo
    crn
    ctg
    cfv
    #
    @10
    crest
    co
    #
    @11
    wph
    @15
    cB
    cpnf
    cioo
    co
    #
    @10
    cin
    #
    @32
    wph
    vx
    @15
    @34
    wph
    vx
    cv
    #
    @15
    wcel
    #
    @35
    @34
    wcel
    #
    wph
    @15
    @34
    @35
    wph
    @15
    @33
    @10
    wph
    @19
    cpnf
    cxr
    wcel
    #
    cB
    cB
    cle
    wbr
    #
    cC
    cpnf
    clt
    wbr
    @15
    @33
    wss
    limcresiooub.b
    @38
    wph
    pnfxr
    a1i
    wph
    @19
    @39
    limcresiooub.b
    cB
    xrleid
    syl
    wph
    cC
    limcresiooub.c
    ltpnfd
    cB
    cpnf
    cB
    cC
    iocssioo
    syl22anc
    wph
    @35
    @10
    wcel
    #
    vx
    @15
    wral
    @15
    @10
    wss
    wph
    @40
    vx
    @15
    wph
    @36
    wa
    #
    @35
    cC
    wceq
    #
    @40
    wph
    @42
    @40
    @36
    wph
    @42
    wa
    #
    @35
    cC
    @10
    wph
    @42
    simpr
    #
    wph
    cC
    @10
    wcel
    #
    @42
    wph
    cC
    cr
    wcel
    #
    cC
    @9
    wcel
    @45
    limcresiooub.c
    cC
    cr
    snidg
    cC
    @9
    @7
    elun2
    3syl
    adantr
    eqeltrd
    adantlr
    @41
    @42
    wn
    #
    wa
    #
    wph
    @35
    @0
    wcel
    #
    @40
    wph
    @36
    @47
    simpll
    @48
    cB
    cC
    @35
    @41
    @19
    @47
    wph
    @19
    @36
    limcresiooub.b
    adantr
    #
    adantr
    @41
    @20
    @47
    wph
    @20
    @36
    @23
    adantr
    #
    adantr
    @41
    @35
    cr
    wcel
    #
    @47
    wph
    @15
    cr
    @35
    wph
    @19
    @46
    @15
    cr
    wss
    limcresiooub.b
    limcresiooub.c
    cB
    cC
    iocssre
    syl2anc
    sselda
    adantr
    #
    @41
    cB
    @35
    clt
    wbr
    #
    @47
    @41
    @19
    @20
    @36
    @54
    @50
    @51
    wph
    @36
    simpr
    #
    cB
    cC
    @35
    iocgtlb
    syl3anc
    adantr
    @48
    @35
    cC
    @53
    wph
    @46
    @36
    @47
    limcresiooub.c
    ad2antrr
    @41
    @35
    cC
    cle
    wbr
    #
    @47
    @41
    @19
    @20
    @36
    @56
    @50
    @51
    @55
    cB
    cC
    @35
    iocleub
    syl3anc
    adantr
    @48
    @35
    cC
    @47
    @35
    cC
    wne
    @41
    @35
    cC
    neqne
    adantl
    necomd
    leneltd
    eliood
    wph
    @49
    wa
    @35
    @7
    wcel
    #
    @40
    wph
    @0
    @7
    @35
    @12
    sselda
    @35
    @7
    @9
    elun1
    syl
    syl2anc
    pm2.61dan
    ralrimiva
    vx
    @15
    @10
    dfss3
    sylibr
    ssind
    sseld
    wph
    @37
    @36
    wph
    @37
    wa
    #
    @42
    @36
    wph
    @42
    @36
    @37
    @43
    @35
    cC
    @15
    @44
    wph
    @22
    @42
    @24
    adantr
    eqeltrd
    adantlr
    @58
    @47
    wa
    #
    @0
    @15
    @35
    cB
    cC
    ioossioc
    @59
    cB
    cC
    @35
    wph
    @19
    @37
    @47
    limcresiooub.b
    ad2antrr
    #
    wph
    @20
    @37
    @47
    @23
    ad2antrr
    #
    @37
    @52
    wph
    @47
    @37
    @35
    cB
    cpnf
    @35
    @33
    @10
    elinel1
    #
    elioored
    ad2antlr
    @59
    @19
    @38
    @35
    @33
    wcel
    #
    @54
    @60
    @38
    @59
    pnfxr
    a1i
    @37
    @63
    wph
    @47
    @62
    ad2antlr
    cB
    cpnf
    @35
    ioogtlb
    syl3anc
    @59
    @5
    @20
    @35
    @2
    wcel
    #
    @35
    cC
    clt
    wbr
    wph
    @5
    @37
    @47
    limcresiooub.d
    ad2antrr
    @61
    @37
    @47
    @64
    wph
    @37
    @47
    wa
    @7
    @2
    @35
    @13
    @37
    @40
    @35
    @9
    wcel
    #
    wn
    @57
    @47
    @35
    @33
    @10
    elinel2
    @47
    @42
    @65
    @47
    id
    vx
    cC
    velsn
    sylnibr
    @35
    @7
    @9
    elunnel2
    syl2an
    sseldi
    adantll
    cD
    cC
    @35
    iooltub
    syl3anc
    eliood
    sseldi
    pm2.61dan
    ex
    impbid
    eqrdv
    wph
    @31
    ctop
    wcel
    #
    @28
    @33
    @31
    wcel
    #
    @34
    @32
    wcel
    @66
    wph
    retop
    a1i
    @28
    wph
    @30
    a1i
    @67
    wph
    cB
    cpnf
    iooretop
    a1i
    @33
    @10
    @31
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrd
    wph
    @32
    @8
    cr
    crest
    co
    #
    @10
    crest
    co
    #
    @11
    @31
    @68
    @10
    crest
    @8
    @14
    tgioo2
    oveq1i
    wph
    @27
    @10
    cr
    wss
    cr
    cvv
    wcel
    #
    @69
    @11
    wceq
    @27
    wph
    @29
    a1i
    wph
    @7
    @9
    cr
    @7
    cr
    wss
    wph
    @7
    @2
    cr
    @13
    cD
    cC
    ioossre
    sstri
    a1i
    wph
    cC
    cr
    limcresiooub.c
    snssd
    unssd
    @70
    wph
    reex
    a1i
    @10
    cr
    @8
    ctop
    cvv
    restabs
    syl3anc
    syl5eq
    eleqtrd
    @15
    @11
    isopn3i
    syl2anc
    eqtr2d
    eleqtrd
    limcres
    eqtrd
end
