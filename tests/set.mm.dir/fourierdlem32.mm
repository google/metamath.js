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
include "csn.mm"
include "cun.mm"
include "crest.mm"
include "cc.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "wss.mm"
include "ioosscn.mm"
include "a1i.mm"
include "eqid.mm"
include "cico.mm"
include "cnt.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "leidd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "rexrd.mm"
include "elico2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "ctop.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "ovex.mm"
include "resttop.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "crn.mm"
include "ctg.mm"
include "cmnf.mm"
include "cin.mm"
include "cv.mm"
include "mnfxr.mm"
include "simpr.mm"
include "mpbid.mm"
include "simp1d.mm"
include "mnfltd.mm"
include "simp3d.mm"
include "eliood.mm"
include "simp2d.mm"
include "fourierdlem10.mm"
include "simprd.mm"
include "ltletrd.mm"
include "elind.mm"
include "elinel1.mm"
include "elioore.mm"
include "elinel2.mm"
include "elioo2.mm"
include "impbida.mm"
include "eqrdv.mm"
include "retop.mm"
include "iooretop.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "oveq1d.mm"
include "icossre.mm"
include "reex.mm"
include "restabs.mm"
include "tgioo2.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3eqtr2d.mm"
include "3eltr4d.mm"
include "isopn3i.mm"
include "eleqtrrd.mm"
include "id.mm"
include "eqcomd.mm"
include "uncom.mm"
include "snunioo.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "sneq.mm"
include "uneq1d.mm"
include "sylan9eqr.mm"
include "fveq12d.mm"
include "limcres.mm"
include "eqtr2d.mm"
include "3eltr3d.mm"
include "wn.mm"
include "limcresi.mm"
include "iffalse.mm"
include "ccnp.mm"
include "wral.mm"
include "ccn.mm"
include "ssid.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cncfcn.mm"
include "eleqtrd.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "mp2an.mm"
include "cncnp.mm"
include "sylib.mm"
include "simpld.mm"
include "wne.mm"
include "eqcoms.mm"
include "necon3bi.mm"
include "necomd.mm"
include "leneltd.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspccva.mm"
include "cnplimc.mm"
include "sseldi.mm"
include "pm2.61dan.mm"

theorem fourierdlem32
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cJ: class J
  let cY: class Y
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem32.a: |- ( ph -> A e. RR )
  assume fourierdlem32.b: |- ( ph -> B e. RR )
  assume fourierdlem32.altb: |- ( ph -> A < B )
  assume fourierdlem32.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume fourierdlem32.l: |- ( ph -> R e. ( F limCC A ) )
  assume fourierdlem32.c: |- ( ph -> C e. RR )
  assume fourierdlem32.d: |- ( ph -> D e. RR )
  assume fourierdlem32.cltd: |- ( ph -> C < D )
  assume fourierdlem32.ss: |- ( ph -> ( C (,) D ) C_ ( A (,) B ) )
  assume fourierdlem32.y: |- Y = if ( C = A , R , ( F ` C ) )
  assume fourierdlem32.j: |- J = ( ( TopOpen ` CCfld ) |`t ( A [,) B ) )


  assert |- ( ph -> Y e. ( ( F |` ( C (,) D ) ) limCC C ) )

  proof
    wph
    cC
    cA
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
    cC
    climc
    co
    #
    wcel
    wph
    @0
    wa
    #
    cR
    cF
    cA
    climc
    co
    #
    cY
    @3
    wph
    cR
    @5
    wcel
    @0
    fourierdlem32.l
    adantr
    @0
    cR
    cY
    wceq
    wph
    @0
    cY
    @0
    cR
    cC
    cF
    cfv
    #
    cif
    #
    cR
    fourierdlem32.y
    @0
    cR
    @6
    iftrue
    syl5req
    adantl
    @4
    @3
    @2
    cA
    climc
    co
    #
    @5
    @0
    @3
    @8
    wceq
    wph
    cC
    cA
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
    cA
    @1
    cF
    ccnfld
    ctopn
    cfv
    #
    @9
    cA
    csn
    #
    cun
    #
    crest
    co
    #
    @10
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
    @14
    fourierdlem32.f
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
    fourierdlem32.ss
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
    @13
    eqid
    @4
    cC
    cC
    cD
    cico
    co
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    cA
    @1
    @11
    cun
    #
    @13
    cnt
    cfv
    #
    cfv
    @4
    cC
    @19
    @21
    wph
    cC
    @19
    wcel
    #
    @0
    wph
    @24
    cC
    cr
    wcel
    #
    cC
    cC
    cle
    wbr
    #
    cC
    cD
    clt
    wbr
    #
    fourierdlem32.c
    wph
    cC
    fourierdlem32.c
    leidd
    fourierdlem32.cltd
    wph
    @25
    cD
    cxr
    wcel
    #
    @24
    @25
    @26
    @27
    w3a
    wb
    fourierdlem32.c
    wph
    cD
    fourierdlem32.d
    rexrd
    #
    cC
    cD
    cC
    elico2
    syl2anc
    mpbir3and
    adantr
    @4
    cJ
    ctop
    wcel
    @19
    cJ
    wcel
    @21
    @19
    wceq
    @4
    cJ
    @10
    cA
    cB
    cico
    co
    #
    crest
    co
    #
    ctop
    fourierdlem32.j
    @4
    @10
    ctop
    wcel
    #
    @30
    cvv
    wcel
    #
    @31
    ctop
    wcel
    @10
    @18
    cnfldtop
    #
    @33
    @4
    cA
    cB
    cico
    ovex
    #
    a1i
    @30
    @10
    cvv
    resttop
    sylancr
    syl5eqel
    @4
    cA
    cD
    cico
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    @30
    crest
    co
    #
    @19
    cJ
    wph
    @36
    @38
    wcel
    @0
    wph
    @36
    cmnf
    cD
    cioo
    co
    #
    @30
    cin
    #
    @38
    wph
    vx
    @36
    @40
    wph
    vx
    cv
    #
    @36
    wcel
    #
    @41
    @40
    wcel
    #
    wph
    @42
    wa
    #
    @39
    @30
    @41
    @44
    cmnf
    cD
    @41
    cmnf
    cxr
    wcel
    #
    @44
    mnfxr
    a1i
    wph
    @28
    @42
    @29
    adantr
    #
    @44
    @41
    cr
    wcel
    #
    cA
    @41
    cle
    wbr
    #
    @41
    cD
    clt
    wbr
    #
    @44
    @42
    @47
    @48
    @49
    w3a
    #
    wph
    @42
    simpr
    @44
    cA
    cr
    wcel
    #
    @28
    @42
    @50
    wb
    #
    wph
    @51
    @42
    fourierdlem32.a
    adantr
    #
    @46
    cA
    cD
    @41
    elico2
    #
    syl2anc
    mpbid
    #
    simp1d
    #
    @44
    @41
    @56
    mnfltd
    @44
    @47
    @48
    @49
    @55
    simp3d
    #
    eliood
    @44
    @41
    @30
    wcel
    #
    @47
    @48
    @41
    cB
    clt
    wbr
    #
    @56
    @44
    @47
    @48
    @49
    @55
    simp2d
    @44
    @41
    cD
    cB
    @56
    wph
    cD
    cr
    wcel
    @42
    fourierdlem32.d
    adantr
    wph
    cB
    cr
    wcel
    @42
    fourierdlem32.b
    adantr
    @57
    wph
    cD
    cB
    cle
    wbr
    #
    @42
    wph
    cA
    cC
    cle
    wbr
    #
    @60
    wph
    cA
    cB
    cC
    cD
    fourierdlem32.a
    fourierdlem32.b
    fourierdlem32.c
    fourierdlem32.d
    fourierdlem32.cltd
    fourierdlem32.ss
    fourierdlem10
    #
    simprd
    #
    adantr
    ltletrd
    @44
    @51
    cB
    cxr
    wcel
    #
    @58
    @47
    @48
    @59
    w3a
    #
    wb
    #
    @53
    wph
    @64
    @42
    wph
    cB
    fourierdlem32.b
    rexrd
    #
    adantr
    cA
    cB
    @41
    elico2
    #
    syl2anc
    mpbir3and
    elind
    wph
    @43
    wa
    #
    @42
    @47
    @48
    @49
    @43
    @47
    wph
    @43
    @41
    @39
    wcel
    #
    @47
    @41
    @39
    @30
    elinel1
    #
    @41
    cmnf
    cD
    elioore
    syl
    adantl
    @69
    @47
    @48
    @59
    @69
    @58
    @65
    @43
    @58
    wph
    @41
    @39
    @30
    elinel2
    adantl
    @69
    @51
    @64
    @66
    wph
    @51
    @43
    fourierdlem32.a
    adantr
    #
    wph
    @64
    @43
    @67
    adantr
    @68
    syl2anc
    mpbid
    simp2d
    @69
    @47
    cmnf
    @41
    clt
    wbr
    #
    @49
    @69
    @70
    @47
    @73
    @49
    w3a
    #
    @43
    @70
    wph
    @71
    adantl
    @69
    @45
    @28
    @70
    @74
    wb
    mnfxr
    wph
    @28
    @43
    @29
    adantr
    #
    cmnf
    cD
    @41
    elioo2
    sylancr
    mpbid
    simp3d
    @69
    @51
    @28
    @52
    @72
    @75
    @54
    syl2anc
    mpbir3and
    impbida
    eqrdv
    wph
    @37
    ctop
    wcel
    #
    @33
    @39
    @37
    wcel
    #
    @40
    @38
    wcel
    @76
    wph
    retop
    a1i
    @33
    wph
    @35
    a1i
    @77
    wph
    cmnf
    cD
    iooretop
    a1i
    @39
    @30
    @37
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrd
    adantr
    @4
    cC
    cA
    cD
    cico
    wph
    @0
    simpr
    oveq1d
    wph
    cJ
    @38
    wceq
    @0
    wph
    cJ
    @31
    @10
    cr
    crest
    co
    #
    @30
    crest
    co
    #
    @38
    cJ
    @31
    wceq
    wph
    fourierdlem32.j
    a1i
    wph
    @32
    @30
    cr
    wss
    #
    cr
    cvv
    wcel
    #
    @79
    @31
    wceq
    @32
    wph
    @34
    a1i
    wph
    @51
    @64
    @80
    fourierdlem32.a
    @67
    cA
    cB
    icossre
    syl2anc
    @81
    wph
    reex
    a1i
    @30
    cr
    @10
    ctop
    cvv
    restabs
    syl3anc
    @79
    @38
    wceq
    wph
    @78
    @37
    @30
    crest
    @37
    @78
    @10
    @18
    tgioo2
    eqcomi
    oveq1i
    a1i
    3eqtr2d
    adantr
    3eltr4d
    @19
    cJ
    isopn3i
    syl2anc
    eleqtrrd
    @0
    cA
    cC
    wceq
    wph
    @0
    cC
    cA
    @0
    id
    #
    eqcomd
    adantl
    @4
    @22
    @19
    @23
    @20
    @4
    @13
    cJ
    cnt
    @4
    @13
    @31
    cJ
    @4
    @12
    @30
    @10
    crest
    wph
    @12
    @30
    wceq
    @0
    wph
    @12
    @11
    @9
    cun
    #
    @30
    @9
    @11
    uncom
    wph
    cA
    cxr
    wcel
    #
    @64
    cA
    cB
    clt
    wbr
    @83
    @30
    wceq
    wph
    cA
    fourierdlem32.a
    rexrd
    #
    @67
    fourierdlem32.altb
    cA
    cB
    snunioo
    syl3anc
    syl5eq
    adantr
    oveq2d
    fourierdlem32.j
    syl6eqr
    fveq2d
    @0
    wph
    @22
    cC
    csn
    #
    @1
    cun
    #
    @19
    @0
    @22
    @11
    @1
    cun
    @87
    @1
    @11
    uncom
    @0
    @11
    @86
    @1
    @0
    @86
    @11
    cC
    cA
    sneq
    eqcomd
    uneq1d
    syl5eq
    wph
    cC
    cxr
    wcel
    @28
    @27
    @87
    @19
    wceq
    wph
    cC
    fourierdlem32.c
    rexrd
    @29
    fourierdlem32.cltd
    cC
    cD
    snunioo
    syl3anc
    sylan9eqr
    fveq12d
    3eltr4d
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
    cC
    climc
    co
    #
    @3
    cY
    cC
    @1
    cF
    limcresi
    @89
    cY
    @6
    @90
    @88
    cY
    @6
    wceq
    wph
    @88
    cY
    @7
    @6
    fourierdlem32.y
    @0
    cR
    @6
    iffalse
    syl5eq
    adantl
    @89
    @14
    @6
    @90
    wcel
    #
    @89
    cF
    cC
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
    @14
    @91
    wa
    #
    @89
    cF
    @41
    @93
    cfv
    #
    wcel
    #
    vx
    @9
    wral
    #
    cC
    @9
    wcel
    #
    @95
    wph
    @99
    @88
    wph
    @14
    @99
    wph
    cF
    @92
    @10
    ccn
    co
    #
    wcel
    #
    @14
    @99
    wa
    #
    wph
    cF
    @15
    @101
    fourierdlem32.f
    wph
    @16
    cc
    cc
    wss
    #
    @15
    @101
    wceq
    @17
    @104
    wph
    cc
    ssid
    a1i
    @9
    cc
    @10
    @92
    @10
    @18
    @92
    eqid
    #
    @10
    cc
    crest
    co
    #
    @10
    @32
    @106
    @10
    wceq
    @34
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
    @92
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
    @102
    @103
    wb
    @108
    @16
    @107
    @10
    @18
    cnfldtopon
    #
    @17
    @9
    @10
    cc
    resttopon
    mp2an
    @109
    vx
    cF
    @92
    @10
    @9
    cc
    cncnp
    mp2an
    sylib
    simprd
    adantr
    @89
    cA
    cB
    cC
    wph
    @84
    @88
    @85
    adantr
    wph
    @64
    @88
    @67
    adantr
    wph
    @25
    @88
    fourierdlem32.c
    adantr
    #
    @89
    cA
    cC
    wph
    @51
    @88
    fourierdlem32.a
    adantr
    @110
    wph
    @61
    @88
    wph
    @61
    @60
    @62
    simpld
    adantr
    @89
    cA
    cC
    @88
    cA
    cC
    wne
    wph
    @0
    cA
    cC
    @0
    cC
    cA
    @82
    eqcoms
    necon3bi
    adantl
    necomd
    leneltd
    wph
    cC
    cB
    clt
    wbr
    @88
    wph
    cC
    cD
    cB
    fourierdlem32.c
    fourierdlem32.d
    fourierdlem32.b
    fourierdlem32.cltd
    @63
    ltletrd
    adantr
    eliood
    #
    @98
    @95
    vx
    cC
    @9
    @41
    cC
    wceq
    @97
    @94
    cF
    @41
    cC
    @93
    fveq2
    eleq2d
    rspccva
    syl2anc
    @89
    @16
    @100
    @95
    @96
    wb
    @17
    @111
    @9
    cC
    cF
    @92
    @10
    @18
    @105
    cnplimc
    sylancr
    mpbid
    simprd
    eqeltrd
    sseldi
    pm2.61dan
end
