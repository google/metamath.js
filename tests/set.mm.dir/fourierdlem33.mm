include "wceq.mm"
include "cioo.mm"
include "co.mm"
include "cres.mm"
include "climc.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "cfv.mm"
include "cif.mm"
include "iftrue.mm"
include "syl5req.mm"
include "adantl.mm"
include "oveq2.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cc.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "wss.mm"
include "ioosscn.mm"
include "a1i.mm"
include "eqid.mm"
include "cioc.mm"
include "cnt.mm"
include "csn.mm"
include "cun.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "leidd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "rexrd.mm"
include "elioc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "eqcom.mm"
include "biimpi.mm"
include "ctop.mm"
include "crest.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "snunioo2.mm"
include "syl3anc.mm"
include "ovex.mm"
include "eqeltrd.mm"
include "resttop.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "crn.mm"
include "ctg.mm"
include "cpnf.mm"
include "cin.mm"
include "cv.mm"
include "pnfxr.mm"
include "simpr.mm"
include "mpbid.mm"
include "simp1d.mm"
include "simp2d.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "fourierdlem10.mm"
include "simpld.mm"
include "lelttrd.mm"
include "simp3d.mm"
include "elind.mm"
include "elinel1.mm"
include "elioore.mm"
include "ioogtlb.mm"
include "elinel2.mm"
include "impbida.mm"
include "eqrdv.mm"
include "retop.mm"
include "iooretop.mm"
include "elrestr.mm"
include "oveq2d.mm"
include "tgioo2.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "iocssre.mm"
include "reex.mm"
include "restabs.mm"
include "syl5reqr.mm"
include "3eqtrrd.mm"
include "eleqtrd.mm"
include "isopn3i.mm"
include "3eltr4d.mm"
include "sneq.mm"
include "eqcomd.mm"
include "uneq2d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "limcres.mm"
include "3eltr3d.mm"
include "wn.mm"
include "limcresi.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "ccnp.mm"
include "wral.mm"
include "ccn.mm"
include "ssid.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cncfcn.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "cncnp.mm"
include "simprd.mm"
include "wne.mm"
include "neqne.mm"
include "necomd.mm"
include "leneltd.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspccva.mm"
include "cnplimc.mm"
include "sseldi.mm"
include "pm2.61dan.mm"

theorem fourierdlem33
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cJ: class J
  let cL: class L
  let cY: class Y
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem33.1: |- ( ph -> A e. RR )
  assume fourierdlem33.2: |- ( ph -> B e. RR )
  assume fourierdlem33.3: |- ( ph -> A < B )
  assume fourierdlem33.4: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume fourierdlem33.5: |- ( ph -> L e. ( F limCC B ) )
  assume fourierdlem33.6: |- ( ph -> C e. RR )
  assume fourierdlem33.7: |- ( ph -> D e. RR )
  assume fourierdlem33.8: |- ( ph -> C < D )
  assume fourierdlem33.ss: |- ( ph -> ( C (,) D ) C_ ( A (,) B ) )
  assume fourierdlem33.y: |- Y = if ( D = B , L , ( F ` D ) )
  assume fourierdlem33.10: |- J = ( ( TopOpen ` CCfld ) |`t ( ( A (,) B ) u. { B } ) )


  assert |- ( ph -> Y e. ( ( F |` ( C (,) D ) ) limCC D ) )

  proof
    wph
    cD
    cB
    wceq
    #
    cY
    cF
    cC
    cD
    cioo
    co
    #
    cres
    #
    cD
    climc
    co
    #
    wcel
    wph
    @0
    wa
    #
    cL
    cF
    cB
    climc
    co
    #
    cY
    @3
    wph
    cL
    @5
    wcel
    @0
    fourierdlem33.5
    adantr
    @0
    cL
    cY
    wceq
    wph
    @0
    cY
    @0
    cL
    cD
    cF
    cfv
    #
    cif
    #
    cL
    fourierdlem33.y
    @0
    cL
    @6
    iftrue
    syl5req
    adantl
    @4
    @3
    @2
    cB
    climc
    co
    #
    @5
    @0
    @3
    @8
    wceq
    wph
    cD
    cB
    @2
    climc
    oveq2
    adantl
    @4
    cA
    cB
    cioo
    co
    #
    cB
    @1
    cF
    cJ
    ccnfld
    ctopn
    cfv
    #
    wph
    @9
    cc
    cF
    wf
    #
    @0
    wph
    cF
    @9
    cc
    ccncf
    co
    #
    wcel
    @11
    fourierdlem33.4
    @9
    cc
    cF
    cncff
    syl
    adantr
    wph
    @1
    @9
    wss
    @0
    fourierdlem33.ss
    adantr
    @9
    cc
    wss
    #
    @4
    cA
    cB
    ioosscn
    #
    a1i
    @10
    eqid
    #
    fourierdlem33.10
    @4
    cB
    cC
    cD
    cioc
    co
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    @1
    cB
    csn
    #
    cun
    #
    @17
    cfv
    @4
    cD
    @16
    cB
    @18
    wph
    cD
    @16
    wcel
    #
    @0
    wph
    @21
    cD
    cr
    wcel
    #
    cC
    cD
    clt
    wbr
    #
    cD
    cD
    cle
    wbr
    #
    fourierdlem33.7
    fourierdlem33.8
    wph
    cD
    fourierdlem33.7
    leidd
    wph
    cC
    cxr
    wcel
    #
    @22
    @21
    @22
    @23
    @24
    w3a
    wb
    wph
    cC
    fourierdlem33.6
    rexrd
    #
    fourierdlem33.7
    cC
    cD
    cD
    elioc2
    syl2anc
    mpbir3and
    adantr
    @0
    cB
    cD
    wceq
    #
    wph
    @0
    @27
    cD
    cB
    eqcom
    biimpi
    adantl
    @4
    cJ
    ctop
    wcel
    #
    @16
    cJ
    wcel
    @18
    @16
    wceq
    wph
    @28
    @0
    wph
    cJ
    @10
    @9
    @19
    cun
    #
    crest
    co
    #
    ctop
    fourierdlem33.10
    wph
    @10
    ctop
    wcel
    #
    @29
    cvv
    wcel
    @30
    ctop
    wcel
    @10
    @15
    cnfldtop
    #
    wph
    @29
    cA
    cB
    cioc
    co
    #
    cvv
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    @29
    @33
    wceq
    wph
    cA
    fourierdlem33.1
    rexrd
    #
    wph
    cB
    fourierdlem33.2
    rexrd
    #
    fourierdlem33.3
    cA
    cB
    snunioo2
    syl3anc
    #
    @33
    cvv
    wcel
    #
    wph
    cA
    cB
    cioc
    ovex
    a1i
    #
    eqeltrd
    @29
    @10
    cvv
    resttop
    sylancr
    syl5eqel
    adantr
    @4
    @16
    cioo
    crn
    ctg
    cfv
    #
    @33
    crest
    co
    #
    cJ
    @4
    @16
    cC
    cB
    cioc
    co
    #
    @42
    @0
    @16
    @43
    wceq
    wph
    cD
    cB
    cC
    cioc
    oveq2
    adantl
    wph
    @43
    @42
    wcel
    @0
    wph
    @43
    cC
    cpnf
    cioo
    co
    #
    @33
    cin
    #
    @42
    wph
    vx
    @43
    @45
    wph
    vx
    cv
    #
    @43
    wcel
    #
    @46
    @45
    wcel
    #
    wph
    @47
    wa
    #
    @44
    @33
    @46
    @49
    cC
    cpnf
    @46
    wph
    @25
    @47
    @26
    adantr
    #
    cpnf
    cxr
    wcel
    #
    @49
    pnfxr
    a1i
    @49
    @46
    cr
    wcel
    #
    cC
    @46
    clt
    wbr
    #
    @46
    cB
    cle
    wbr
    #
    @49
    @47
    @52
    @53
    @54
    w3a
    #
    wph
    @47
    simpr
    @49
    @25
    cB
    cr
    wcel
    #
    @47
    @55
    wb
    #
    @50
    wph
    @56
    @47
    fourierdlem33.2
    adantr
    #
    cC
    cB
    @46
    elioc2
    #
    syl2anc
    mpbid
    #
    simp1d
    #
    @49
    @52
    @53
    @54
    @60
    simp2d
    #
    @49
    @46
    @61
    ltpnfd
    eliood
    @49
    @46
    @33
    wcel
    #
    @52
    cA
    @46
    clt
    wbr
    #
    @54
    @61
    @49
    cA
    cC
    @46
    wph
    cA
    cr
    wcel
    @47
    fourierdlem33.1
    adantr
    wph
    cC
    cr
    wcel
    @47
    fourierdlem33.6
    adantr
    @61
    wph
    cA
    cC
    cle
    wbr
    #
    @47
    wph
    @65
    cD
    cB
    cle
    wbr
    #
    wph
    cA
    cB
    cC
    cD
    fourierdlem33.1
    fourierdlem33.2
    fourierdlem33.6
    fourierdlem33.7
    fourierdlem33.8
    fourierdlem33.ss
    fourierdlem10
    #
    simpld
    #
    adantr
    @62
    lelttrd
    @49
    @52
    @53
    @54
    @60
    simp3d
    @49
    @34
    @56
    @63
    @52
    @64
    @54
    w3a
    #
    wb
    #
    wph
    @34
    @47
    @36
    adantr
    @58
    cA
    cB
    @46
    elioc2
    #
    syl2anc
    mpbir3and
    elind
    wph
    @48
    wa
    #
    @47
    @52
    @53
    @54
    @48
    @52
    wph
    @48
    @46
    @44
    wcel
    #
    @52
    @46
    @44
    @33
    elinel1
    #
    @46
    cC
    cpnf
    elioore
    syl
    adantl
    @72
    @25
    @51
    @73
    @53
    wph
    @25
    @48
    @26
    adantr
    #
    @51
    @72
    pnfxr
    a1i
    @48
    @73
    wph
    @74
    adantl
    cC
    cpnf
    @46
    ioogtlb
    syl3anc
    @72
    @52
    @64
    @54
    @72
    @63
    @69
    @48
    @63
    wph
    @46
    @44
    @33
    elinel2
    adantl
    @72
    @34
    @56
    @70
    wph
    @34
    @48
    @36
    adantr
    wph
    @56
    @48
    fourierdlem33.2
    adantr
    #
    @71
    syl2anc
    mpbid
    simp3d
    @72
    @25
    @56
    @57
    @75
    @76
    @59
    syl2anc
    mpbir3and
    impbida
    eqrdv
    wph
    @41
    ctop
    wcel
    #
    @39
    @44
    @41
    wcel
    #
    @45
    @42
    wcel
    @77
    wph
    retop
    a1i
    @40
    @78
    wph
    cC
    cpnf
    iooretop
    a1i
    @44
    @33
    @41
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrd
    adantr
    eqeltrd
    wph
    @42
    cJ
    wceq
    @0
    wph
    cJ
    @30
    @10
    @33
    crest
    co
    #
    @42
    cJ
    @30
    wceq
    wph
    fourierdlem33.10
    a1i
    wph
    @29
    @33
    @10
    crest
    @38
    oveq2d
    wph
    @42
    @10
    cr
    crest
    co
    #
    @33
    crest
    co
    #
    @79
    @80
    @41
    @33
    crest
    @41
    @80
    @10
    @15
    tgioo2
    eqcomi
    oveq1i
    wph
    @31
    @33
    cr
    wss
    #
    cr
    cvv
    wcel
    #
    @81
    @79
    wceq
    @31
    wph
    @32
    a1i
    wph
    @34
    @56
    @82
    @36
    fourierdlem33.2
    cA
    cB
    iocssre
    syl2anc
    @83
    wph
    reex
    a1i
    @33
    cr
    @10
    ctop
    cvv
    restabs
    syl3anc
    syl5reqr
    3eqtrrd
    adantr
    eleqtrd
    @16
    cJ
    isopn3i
    syl2anc
    3eltr4d
    @4
    @16
    @20
    @17
    @4
    @20
    @1
    cD
    csn
    #
    cun
    #
    @16
    @0
    @20
    @85
    wceq
    wph
    @0
    @19
    @84
    @1
    @0
    @84
    @19
    cD
    cB
    sneq
    eqcomd
    uneq2d
    adantl
    wph
    @85
    @16
    wceq
    #
    @0
    wph
    @25
    cD
    cxr
    wcel
    @23
    @86
    @26
    wph
    cD
    fourierdlem33.7
    rexrd
    fourierdlem33.8
    cC
    cD
    snunioo2
    syl3anc
    adantr
    eqtr2d
    fveq2d
    eleqtrd
    limcres
    eqtr2d
    3eltr3d
    wph
    @0
    wn
    #
    wa
    #
    cF
    cD
    climc
    co
    #
    @3
    cY
    cD
    @1
    cF
    limcresi
    @88
    cY
    @6
    @89
    @87
    cY
    @6
    wceq
    wph
    @87
    cY
    @7
    @6
    fourierdlem33.y
    @0
    cL
    @6
    iffalse
    syl5eq
    adantl
    @88
    @11
    @6
    @89
    wcel
    #
    @88
    cF
    cD
    @10
    @9
    crest
    co
    #
    @10
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @11
    @90
    wa
    #
    @88
    cF
    @46
    @92
    cfv
    #
    wcel
    #
    vx
    @9
    wral
    #
    cD
    @9
    wcel
    #
    @94
    wph
    @98
    @87
    wph
    @11
    @98
    wph
    cF
    @91
    @10
    ccn
    co
    #
    wcel
    #
    @11
    @98
    wa
    #
    wph
    cF
    @12
    @100
    fourierdlem33.4
    wph
    @13
    cc
    cc
    wss
    #
    @12
    @100
    wceq
    @14
    @103
    wph
    cc
    ssid
    a1i
    @9
    cc
    @10
    @91
    @10
    @15
    @91
    eqid
    #
    @10
    cc
    crest
    co
    #
    @10
    @31
    @105
    @10
    wceq
    @32
    @10
    ctop
    cc
    unicntop
    restid
    ax-mp
    eqcomi
    cncfcn
    sylancr
    eleqtrd
    wph
    @91
    @9
    ctopon
    cfv
    wcel
    #
    @10
    cc
    ctopon
    cfv
    wcel
    #
    @101
    @102
    wb
    wph
    @107
    @13
    @106
    @10
    @15
    cnfldtopon
    #
    @13
    wph
    @14
    a1i
    @9
    @10
    cc
    resttopon
    sylancr
    @107
    wph
    @108
    a1i
    vx
    cF
    @91
    @10
    @9
    cc
    cncnp
    syl2anc
    mpbid
    simprd
    adantr
    @88
    cA
    cB
    cD
    wph
    @34
    @87
    @36
    adantr
    wph
    @35
    @87
    @37
    adantr
    wph
    @22
    @87
    fourierdlem33.7
    adantr
    #
    wph
    cA
    cD
    clt
    wbr
    @87
    wph
    cA
    cC
    cD
    fourierdlem33.1
    fourierdlem33.6
    fourierdlem33.7
    @68
    fourierdlem33.8
    lelttrd
    adantr
    @88
    cD
    cB
    @109
    wph
    @56
    @87
    fourierdlem33.2
    adantr
    wph
    @66
    @87
    wph
    @65
    @66
    @67
    simprd
    adantr
    @87
    cB
    cD
    wne
    wph
    @87
    cD
    cB
    cD
    cB
    neqne
    necomd
    adantl
    leneltd
    eliood
    #
    @97
    @94
    vx
    cD
    @9
    @46
    cD
    wceq
    @96
    @93
    cF
    @46
    cD
    @92
    fveq2
    eleq2d
    rspccva
    syl2anc
    @88
    @13
    @99
    @94
    @95
    wb
    @14
    @110
    @9
    cD
    cF
    @91
    @10
    @15
    @104
    cnplimc
    sylancr
    mpbid
    simprd
    eqeltrd
    sseldi
    pm2.61dan
end
