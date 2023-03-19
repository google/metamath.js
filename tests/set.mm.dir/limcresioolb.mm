include "cioo.mm"
include "co.mm"
include "cres.mm"
include "climc.mm"
include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "iooss2.mm"
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
include "cico.mm"
include "cnt.mm"
include "clt.mm"
include "rexrd.mm"
include "lbico1.mm"
include "syl3anc.mm"
include "wceq.mm"
include "snunioo1.mm"
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
include "cmnf.mm"
include "cv.mm"
include "wa.mm"
include "mnfxr.mm"
include "adantr.mm"
include "cr.mm"
include "icossre.mm"
include "sselda.mm"
include "mnfltd.mm"
include "simpr.mm"
include "icoltub.mm"
include "eliood.mm"
include "snidg.mm"
include "elun2.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "simpll.mm"
include "ad2antrr.mm"
include "icogelb.mm"
include "wne.mm"
include "neqne.mm"
include "adantl.mm"
include "leneltd.mm"
include "elun1.mm"
include "pm2.61dan.mm"
include "elind.mm"
include "ioossico.mm"
include "elinel1.mm"
include "elioored.mm"
include "ad2antlr.mm"
include "elinel2.mm"
include "id.mm"
include "velsn.mm"
include "sylnibr.mm"
include "elunnel2.mm"
include "syl2an.mm"
include "sseldi.mm"
include "adantll.mm"
include "ioogtlb.mm"
include "iooltub.mm"
include "impbida.mm"
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

theorem limcresioolb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vx: setvar x
  assume limcresioolb.f: |- ( ph -> F : A --> CC )
  assume limcresioolb.b: |- ( ph -> B e. RR )
  assume limcresioolb.c: |- ( ph -> C e. RR* )
  assume limcresioolb.bltc: |- ( ph -> B < C )
  assume limcresioolb.bcss: |- ( ph -> ( B (,) C ) C_ A )
  assume limcresioolb.d: |- ( ph -> D e. RR* )
  assume limcresioolb.cled: |- ( ph -> C <_ D )


  assert |- ( ph -> ( ( F |` ( B (,) C ) ) limCC B ) = ( ( F |` ( B (,) D ) ) limCC B ) )

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
    cB
    climc
    co
    cF
    cB
    cD
    cioo
    co
    #
    cres
    #
    @0
    cres
    #
    cB
    climc
    co
    @3
    cB
    climc
    co
    wph
    @1
    @4
    cB
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
    cC
    cD
    cle
    wbr
    @0
    @2
    wss
    limcresioolb.d
    limcresioolb.cled
    cB
    cC
    cD
    iooss2
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
    cB
    @0
    @3
    ccnfld
    ctopn
    cfv
    #
    @7
    cB
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
    limcresioolb.f
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
    limcresioolb.bcss
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
    cB
    cD
    ioosscn
    sstri
    a1i
    @8
    eqid
    #
    @11
    eqid
    wph
    cB
    cB
    cC
    cico
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
    cB
    @15
    wcel
    #
    wph
    cB
    limcresioolb.b
    rexrd
    #
    limcresioolb.c
    limcresioolb.bltc
    cB
    cC
    lbico1
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
    @23
    limcresioolb.c
    limcresioolb.bltc
    cB
    cC
    snunioo1
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
    cB
    cD
    cioo
    ovex
    inex2
    cB
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
    cmnf
    cC
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
    @36
    wa
    #
    @33
    @10
    @35
    @38
    cmnf
    cC
    @35
    cmnf
    cxr
    wcel
    #
    @38
    mnfxr
    a1i
    wph
    @20
    @36
    limcresioolb.c
    adantr
    #
    wph
    @15
    cr
    @35
    wph
    cB
    cr
    wcel
    #
    @20
    @15
    cr
    wss
    limcresioolb.b
    limcresioolb.c
    cB
    cC
    icossre
    syl2anc
    sselda
    #
    @38
    @35
    @42
    mnfltd
    @38
    @19
    @20
    @36
    @35
    cC
    clt
    wbr
    #
    wph
    @19
    @36
    @23
    adantr
    #
    @40
    wph
    @36
    simpr
    #
    cB
    cC
    @35
    icoltub
    syl3anc
    #
    eliood
    @38
    @35
    cB
    wceq
    #
    @35
    @10
    wcel
    #
    wph
    @47
    @48
    @36
    wph
    @47
    wa
    #
    @35
    cB
    @10
    wph
    @47
    simpr
    #
    wph
    cB
    @10
    wcel
    #
    @47
    wph
    @41
    cB
    @9
    wcel
    @51
    limcresioolb.b
    cB
    cr
    snidg
    cB
    @9
    @7
    elun2
    3syl
    adantr
    eqeltrd
    adantlr
    @38
    @47
    wn
    #
    wa
    #
    wph
    @35
    @0
    wcel
    #
    @48
    wph
    @36
    @52
    simpll
    @53
    cB
    cC
    @35
    @38
    @19
    @52
    @44
    adantr
    @38
    @20
    @52
    @40
    adantr
    @38
    @35
    cr
    wcel
    #
    @52
    @42
    adantr
    #
    @53
    cB
    @35
    wph
    @41
    @36
    @52
    limcresioolb.b
    ad2antrr
    @56
    @38
    cB
    @35
    cle
    wbr
    #
    @52
    @38
    @19
    @20
    @36
    @57
    @44
    @40
    @45
    cB
    cC
    @35
    icogelb
    syl3anc
    adantr
    @52
    @35
    cB
    wne
    @38
    @35
    cB
    neqne
    adantl
    leneltd
    @38
    @43
    @52
    @46
    adantr
    eliood
    wph
    @54
    wa
    @35
    @7
    wcel
    #
    @48
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
    elind
    wph
    @37
    wa
    #
    @47
    @36
    wph
    @47
    @36
    @37
    @49
    @35
    cB
    @15
    @50
    wph
    @22
    @47
    @24
    adantr
    eqeltrd
    adantlr
    @59
    @52
    wa
    #
    @0
    @15
    @35
    cB
    cC
    ioossico
    @60
    cB
    cC
    @35
    wph
    @19
    @37
    @52
    @23
    ad2antrr
    #
    wph
    @20
    @37
    @52
    limcresioolb.c
    ad2antrr
    @37
    @55
    wph
    @52
    @37
    @35
    cmnf
    cC
    @35
    @33
    @10
    elinel1
    #
    elioored
    ad2antlr
    @60
    @19
    @5
    @35
    @2
    wcel
    #
    cB
    @35
    clt
    wbr
    @61
    wph
    @5
    @37
    @52
    limcresioolb.d
    ad2antrr
    @37
    @52
    @63
    wph
    @37
    @52
    wa
    @7
    @2
    @35
    @13
    @37
    @48
    @35
    @9
    wcel
    #
    wn
    @58
    @52
    @35
    @33
    @10
    elinel2
    @52
    @47
    @64
    @52
    id
    vx
    cB
    velsn
    sylnibr
    @35
    @7
    @9
    elunnel2
    syl2an
    sseldi
    adantll
    cB
    cD
    @35
    ioogtlb
    syl3anc
    @59
    @43
    @52
    @59
    @39
    @20
    @35
    @33
    wcel
    #
    @43
    @39
    @59
    mnfxr
    a1i
    wph
    @20
    @37
    limcresioolb.c
    adantr
    @37
    @65
    wph
    @62
    adantl
    cmnf
    cC
    @35
    iooltub
    syl3anc
    adantr
    eliood
    sseldi
    pm2.61dan
    impbida
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
    cmnf
    cC
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
    cB
    cD
    ioossre
    sstri
    a1i
    wph
    cB
    cr
    limcresioolb.b
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
