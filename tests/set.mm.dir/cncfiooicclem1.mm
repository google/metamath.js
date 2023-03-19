include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "ccn.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "wceq.mm"
include "cif.mm"
include "wa.mm"
include "climc.mm"
include "limccl.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "cioo.mm"
include "simplll.mm"
include "cpr.mm"
include "wo.mm"
include "orel1.mm"
include "con3dimp.mm"
include "vex.mm"
include "elpr.mm"
include "sylnibr.mm"
include "adantll.mm"
include "cun.mm"
include "simpllr.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "syl.mm"
include "ltled.mm"
include "prunioo.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "elun.mm"
include "sylib.mm"
include "orel2.mm"
include "sylc.mm"
include "cncff.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "ifclda.mm"
include "fmptdf.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "cres.mm"
include "cmpt.mm"
include "wss.mm"
include "ioossicc.mm"
include "fssres.mm"
include "sylancl.mm"
include "feqmptd.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfres.mm"
include "nffv.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "a1i.mm"
include "fvres.mm"
include "adantl.mm"
include "simpr.mm"
include "adantr.mm"
include "ifcld.mm"
include "fvmpt2.mm"
include "wne.mm"
include "clt.mm"
include "cr.mm"
include "w3a.mm"
include "elioo4g.mm"
include "biimpi.mm"
include "simpld.mm"
include "simp1d.mm"
include "elioore.mm"
include "eliooord.mm"
include "xrltne.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "simprd.mm"
include "ltned.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "mpteq2da.mm"
include "ioosscn.mm"
include "ssid.mm"
include "eqid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "3eltr3d.mm"
include "eqeltrd.mm"
include "cuni.mm"
include "restuni.mm"
include "mp2an.mm"
include "cncnpi.mm"
include "sylan.mm"
include "cvv.mm"
include "ovex.mm"
include "restabs.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "cnt.mm"
include "wb.mm"
include "resttop.mm"
include "iccssred.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sylancr.mm"
include "sseqtrd.mm"
include "crn.mm"
include "ctg.mm"
include "cdif.mm"
include "cin.mm"
include "retop.mm"
include "ioossre.mm"
include "difss.mm"
include "unssi.mm"
include "ssun1.mm"
include "uniretop.mm"
include "ntrss.mm"
include "ioontr.mm"
include "syl6eleqr.mm"
include "sseldd.mm"
include "elind.mm"
include "restntr.mm"
include "tgioo2.mm"
include "reex.mm"
include "fveq2d.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "elpri.mm"
include "lbicc2.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "eqtr2d.mm"
include "limciccioolb.mm"
include "cnplimc.mm"
include "mpbir2and.mm"
include "leidd.mm"
include "eliccd.mm"
include "iftruei.mm"
include "syl5eqel.mm"
include "jca.mm"
include "wi.mm"
include "nfv.mm"
include "nfeq1.mm"
include "nfim.mm"
include "eleq1.mm"
include "eqtr2.mm"
include "iffalse.mm"
include "df-ne.mm"
include "pm13.18.mm"
include "sylan2br.mm"
include "syl6req.mm"
include "pm2.61dan.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtoclg1f.mm"
include "gtned.mm"
include "limcicciooub.mm"
include "jaodan.mm"
include "sylan2.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "cncnp.mm"

theorem cncfiooicclem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let vy: setvar y
  let vk: setvar k
  assume cncfiooicclem1.x: |- F/ x ph
  assume cncfiooicclem1.g: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( F ` x ) ) ) )
  assume cncfiooicclem1.a: |- ( ph -> A e. RR )
  assume cncfiooicclem1.b: |- ( ph -> B e. RR )
  assume cncfiooicclem1.altb: |- ( ph -> A < B )
  assume cncfiooicclem1.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume cncfiooicclem1.l: |- ( ph -> L e. ( F limCC B ) )
  assume cncfiooicclem1.r: |- ( ph -> R e. ( F limCC A ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint L x
  disjoint R x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint G y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> G e. ( ( A [,] B ) -cn-> CC ) )

  proof
    wph
    cG
    ccnfld
    ctopn
    cfv
    #
    cA
    cB
    cicc
    co
    #
    crest
    co
    #
    @0
    ccn
    co
    #
    @1
    cc
    ccncf
    co
    #
    wph
    cG
    @3
    wcel
    #
    @1
    cc
    cG
    wf
    #
    cG
    vy
    cv
    #
    @2
    @0
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vy
    @1
    wral
    #
    wph
    vx
    @1
    vx
    cv
    #
    cA
    wceq
    #
    cR
    @12
    cB
    wceq
    #
    cL
    @12
    cF
    cfv
    #
    cif
    #
    cif
    #
    cc
    cG
    cncfiooicclem1.x
    wph
    @12
    @1
    wcel
    #
    wa
    #
    @13
    cR
    @16
    cc
    wph
    cR
    cc
    wcel
    #
    @18
    @13
    wph
    cF
    cA
    climc
    co
    #
    cc
    cR
    cA
    cF
    limccl
    cncfiooicclem1.r
    sseldi
    #
    ad2antrr
    @19
    @13
    wn
    #
    wa
    #
    @14
    cL
    @15
    cc
    wph
    cL
    cc
    wcel
    #
    @18
    @23
    @14
    wph
    cF
    cB
    climc
    co
    #
    cc
    cL
    cB
    cF
    limccl
    cncfiooicclem1.l
    sseldi
    #
    ad3antrrr
    @24
    @14
    wn
    #
    wa
    #
    wph
    @12
    cA
    cB
    cioo
    co
    #
    wcel
    #
    @15
    cc
    wcel
    #
    wph
    @18
    @23
    @28
    simplll
    #
    @29
    @12
    cA
    cB
    cpr
    #
    wcel
    #
    wn
    #
    @31
    @35
    wo
    #
    @31
    @23
    @28
    @36
    @19
    @23
    @28
    wa
    @13
    @14
    wo
    #
    @35
    @23
    @38
    @14
    @13
    @14
    orel1
    con3dimp
    @12
    cA
    cB
    vx
    vex
    elpr
    sylnibr
    adantll
    @29
    @12
    @30
    @34
    cun
    #
    wcel
    @37
    @29
    @12
    @1
    @39
    wph
    @18
    @23
    @28
    simpllr
    @29
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
    cle
    wbr
    #
    @39
    @1
    wceq
    #
    @29
    wph
    @40
    @33
    wph
    cA
    cncfiooicclem1.a
    rexrd
    #
    syl
    @29
    wph
    @41
    @33
    wph
    cB
    cncfiooicclem1.b
    rexrd
    #
    syl
    @29
    wph
    @42
    @33
    wph
    cA
    cB
    cncfiooicclem1.a
    cncfiooicclem1.b
    cncfiooicclem1.altb
    ltled
    #
    syl
    cA
    cB
    prunioo
    #
    syl3anc
    eleqtrrd
    @12
    @30
    @34
    elun
    sylib
    @35
    @31
    orel2
    sylc
    wph
    @30
    cc
    @12
    cF
    wph
    cF
    @30
    cc
    ccncf
    co
    #
    wcel
    @30
    cc
    cF
    wf
    cncfiooicclem1.f
    @30
    cc
    cF
    cncff
    syl
    #
    ffvelrnda
    #
    syl2anc
    ifclda
    ifclda
    cncfiooicclem1.g
    fmptdf
    #
    wph
    @10
    vy
    @1
    wph
    @7
    @1
    wcel
    #
    @7
    @30
    wcel
    #
    @7
    @34
    wcel
    #
    wo
    #
    @10
    wph
    @55
    @52
    @55
    @7
    @39
    wcel
    wph
    @52
    @7
    @30
    @34
    elun
    wph
    @39
    @1
    @7
    wph
    @40
    @41
    @42
    @43
    @44
    @45
    @46
    @47
    syl3anc
    eleq2d
    syl5bbr
    biimpar
    wph
    @53
    @10
    @54
    wph
    @53
    wa
    #
    @10
    cG
    @30
    cres
    #
    @7
    @2
    @30
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @56
    @57
    @7
    @0
    @30
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    @60
    wph
    @57
    @62
    @0
    ccn
    co
    #
    wcel
    @53
    @57
    @64
    wcel
    wph
    @57
    vx
    @30
    @15
    cmpt
    #
    @65
    wph
    @57
    vy
    @30
    @7
    @57
    cfv
    #
    cmpt
    #
    vx
    @30
    @12
    @57
    cfv
    #
    cmpt
    #
    @66
    wph
    vy
    @30
    cc
    @57
    wph
    @6
    @30
    @1
    wss
    #
    @30
    cc
    @57
    wf
    @51
    cA
    cB
    ioossicc
    #
    @1
    cc
    @30
    cG
    fssres
    sylancl
    feqmptd
    @68
    @70
    wceq
    wph
    vy
    vx
    @30
    @67
    @69
    vx
    @7
    @57
    vx
    cG
    @30
    vx
    cG
    vx
    @1
    @17
    cmpt
    cncfiooicclem1.g
    vx
    @1
    @17
    nfmpt1
    nfcxfr
    #
    vx
    @30
    nfcv
    nfres
    vx
    @7
    nfcv
    nffv
    vy
    @12
    @57
    vy
    @57
    nfcv
    vy
    @12
    nfcv
    nffv
    @7
    @12
    @57
    fveq2
    cbvmpt
    a1i
    wph
    vx
    @30
    @69
    @15
    cncfiooicclem1.x
    wph
    @31
    wa
    #
    @69
    @12
    cG
    cfv
    #
    @17
    @15
    @31
    @69
    @75
    wceq
    wph
    @12
    @30
    cG
    fvres
    adantl
    @74
    @18
    @17
    cc
    wcel
    #
    @75
    @17
    wceq
    #
    @74
    @30
    @1
    @12
    @72
    wph
    @31
    simpr
    sseldi
    @74
    @13
    cR
    @16
    cc
    wph
    @20
    @31
    @22
    adantr
    @74
    @14
    cL
    @15
    cc
    wph
    @25
    @31
    @14
    @27
    ad2antrr
    @74
    @32
    @28
    @50
    adantr
    ifclda
    ifcld
    vx
    @1
    @17
    cc
    cG
    cncfiooicclem1.g
    fvmpt2
    #
    syl2anc
    @74
    @17
    @16
    @15
    @74
    @13
    cR
    @16
    @74
    @12
    cA
    @31
    @12
    cA
    wne
    #
    wph
    @31
    @40
    @12
    cxr
    wcel
    cA
    @12
    clt
    wbr
    #
    @79
    @31
    @40
    @41
    @12
    cr
    wcel
    #
    @31
    @40
    @41
    @81
    w3a
    #
    @80
    @12
    cB
    clt
    wbr
    #
    wa
    #
    @31
    @82
    @84
    wa
    cA
    cB
    @12
    elioo4g
    biimpi
    simpld
    simp1d
    @31
    @12
    @12
    cA
    cB
    elioore
    #
    rexrd
    @31
    @80
    @83
    @12
    cA
    cB
    eliooord
    #
    simpld
    cA
    @12
    xrltne
    syl3anc
    adantl
    neneqd
    iffalsed
    @31
    @16
    @15
    wceq
    wph
    @31
    @14
    cL
    @15
    @31
    @12
    cB
    @31
    @12
    cB
    @85
    @31
    @80
    @83
    @86
    simprd
    ltned
    neneqd
    iffalsed
    adantl
    eqtrd
    3eqtrd
    mpteq2da
    3eqtrd
    #
    wph
    cF
    @48
    @66
    @65
    cncfiooicclem1.f
    wph
    vx
    @30
    cc
    cF
    @49
    feqmptd
    #
    wph
    @30
    cc
    wss
    #
    cc
    cc
    wss
    #
    @48
    @65
    wceq
    @89
    wph
    cA
    cB
    ioosscn
    #
    a1i
    cc
    ssid
    #
    @30
    cc
    @0
    @62
    @0
    @0
    eqid
    #
    @62
    eqid
    @0
    cc
    crest
    co
    #
    @0
    @0
    ctop
    wcel
    #
    @94
    @0
    wceq
    @0
    @93
    cnfldtop
    #
    @0
    ctop
    cc
    unicntop
    restid
    ax-mp
    eqcomi
    #
    cncfcn
    sylancl
    3eltr3d
    eqeltrd
    @7
    @57
    @62
    @0
    @30
    @95
    @89
    @30
    @62
    cuni
    wceq
    @96
    @91
    @30
    @0
    cc
    unicntop
    restuni
    mp2an
    cncnpi
    sylan
    @56
    @7
    @63
    @59
    @56
    @62
    @58
    @0
    ccnp
    @56
    @58
    @62
    @56
    @95
    @71
    @1
    cvv
    wcel
    #
    @58
    @62
    wceq
    @95
    @56
    @96
    a1i
    @71
    @56
    @72
    a1i
    #
    @98
    @56
    cA
    cB
    cicc
    ovex
    #
    a1i
    @30
    @1
    @0
    ctop
    cvv
    restabs
    syl3anc
    eqcomd
    oveq1d
    fveq1d
    eleqtrd
    @56
    @2
    ctop
    wcel
    #
    @30
    @2
    cuni
    #
    wss
    #
    @7
    @30
    @2
    cnt
    cfv
    #
    cfv
    #
    wcel
    @102
    cc
    cG
    wf
    #
    @10
    @61
    wb
    @101
    @56
    @95
    @98
    @101
    @96
    @100
    @1
    @0
    cvv
    resttop
    mp2an
    a1i
    wph
    @103
    @53
    wph
    @30
    @1
    @102
    @71
    wph
    @72
    a1i
    wph
    @95
    @1
    cc
    wss
    #
    @1
    @102
    wceq
    @96
    wph
    @1
    cr
    cc
    wph
    cA
    cB
    cncfiooicclem1.a
    cncfiooicclem1.b
    iccssred
    #
    ax-resscn
    syl6ss
    #
    @1
    @0
    cc
    unicntop
    restuni
    sylancr
    #
    sseqtrd
    adantr
    @56
    @7
    @30
    cioo
    crn
    ctg
    cfv
    #
    @1
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @105
    @56
    @7
    @30
    cr
    @1
    cdif
    #
    cun
    #
    @111
    cnt
    cfv
    #
    cfv
    #
    @1
    cin
    #
    @114
    @56
    @118
    @1
    @7
    @56
    @30
    @117
    cfv
    #
    @118
    @7
    @56
    @111
    ctop
    wcel
    #
    @116
    cr
    wss
    #
    @30
    @116
    wss
    #
    @120
    @118
    wss
    @121
    @56
    retop
    a1i
    #
    @122
    @56
    @30
    @115
    cr
    cA
    cB
    ioossre
    cr
    @1
    difss
    unssi
    a1i
    @123
    @56
    @30
    @115
    ssun1
    a1i
    @116
    @30
    @111
    cr
    uniretop
    ntrss
    syl3anc
    @56
    @7
    @30
    @120
    wph
    @53
    simpr
    #
    cA
    cB
    ioontr
    syl6eleqr
    sseldd
    @56
    @30
    @1
    @7
    @72
    @125
    sseldi
    elind
    @56
    @121
    @1
    cr
    wss
    #
    @71
    @114
    @119
    wceq
    @124
    wph
    @126
    @53
    @108
    adantr
    @99
    @30
    @111
    @112
    cr
    @1
    uniretop
    @112
    eqid
    restntr
    syl3anc
    eleqtrrd
    wph
    @114
    @105
    wceq
    @53
    wph
    @30
    @113
    @104
    wph
    @112
    @2
    cnt
    wph
    @112
    @0
    cr
    crest
    co
    #
    @1
    crest
    co
    #
    @2
    wph
    @111
    @127
    @1
    crest
    @111
    @127
    wceq
    wph
    @0
    @93
    tgioo2
    a1i
    oveq1d
    wph
    @95
    @126
    cr
    cvv
    wcel
    #
    @128
    @2
    wceq
    @95
    wph
    @96
    a1i
    @108
    @129
    wph
    reex
    a1i
    @1
    cr
    @0
    ctop
    cvv
    restabs
    syl3anc
    eqtrd
    fveq2d
    fveq1d
    adantr
    eleqtrd
    wph
    @106
    @53
    wph
    @6
    @106
    @51
    wph
    @1
    @102
    cc
    cG
    @110
    feq2d
    mpbid
    adantr
    @30
    @7
    cG
    @2
    @0
    @102
    cc
    @102
    eqid
    unicntop
    cnprest
    syl22anc
    mpbird
    @54
    wph
    @7
    cA
    wceq
    #
    @7
    cB
    wceq
    #
    wo
    @10
    @7
    cA
    cB
    elpri
    wph
    @130
    @10
    @131
    wph
    @130
    wa
    cG
    cA
    @8
    cfv
    #
    @9
    wph
    cG
    @132
    wcel
    #
    @130
    wph
    @133
    @6
    cA
    cG
    cfv
    #
    cG
    cA
    climc
    co
    #
    wcel
    #
    @51
    wph
    @134
    cR
    @135
    wph
    cA
    @1
    wcel
    #
    cR
    @21
    wcel
    @134
    cR
    wceq
    wph
    @40
    @41
    @42
    @137
    @44
    @45
    @46
    cA
    cB
    lbicc2
    syl3anc
    #
    cncfiooicclem1.r
    vx
    cA
    @17
    cR
    @1
    @21
    cG
    @13
    cR
    @16
    iftrue
    #
    cncfiooicclem1.g
    fvmptg
    syl2anc
    wph
    cR
    @57
    cA
    climc
    co
    #
    @135
    wph
    cR
    @21
    @140
    cncfiooicclem1.r
    wph
    cF
    @57
    cA
    climc
    wph
    @57
    @66
    cF
    @87
    wph
    cF
    @66
    @88
    eqcomd
    eqtr2d
    #
    oveq1d
    eleqtrd
    wph
    cA
    cB
    cG
    cncfiooicclem1.a
    cncfiooicclem1.b
    cncfiooicclem1.altb
    @51
    limciccioolb
    eleqtrd
    eqeltrd
    wph
    @107
    @137
    @133
    @6
    @136
    wa
    wb
    @109
    @138
    @1
    cA
    cG
    @2
    @0
    @93
    @2
    eqid
    #
    cnplimc
    syl2anc
    mpbir2and
    adantr
    @130
    @132
    @9
    wceq
    wph
    @130
    @9
    @132
    @7
    cA
    @8
    fveq2
    eqcomd
    adantl
    eleqtrd
    wph
    @131
    wa
    cG
    cB
    @8
    cfv
    #
    @9
    wph
    cG
    @143
    wcel
    #
    @131
    wph
    @144
    @6
    cB
    cG
    cfv
    #
    cG
    cB
    climc
    co
    #
    wcel
    #
    @51
    wph
    @145
    cL
    @146
    wph
    @145
    cB
    cA
    wceq
    #
    cR
    cB
    cB
    wceq
    #
    cL
    cB
    cF
    cfv
    #
    cif
    #
    cif
    #
    @151
    cL
    wph
    cB
    @1
    wcel
    #
    @153
    @152
    cc
    wcel
    #
    wa
    #
    @145
    @152
    wceq
    #
    wph
    cA
    cB
    cB
    cncfiooicclem1.a
    cncfiooicclem1.b
    cncfiooicclem1.b
    @46
    wph
    cB
    cncfiooicclem1.b
    leidd
    eliccd
    #
    wph
    @153
    @154
    @157
    wph
    @148
    cR
    @151
    cc
    @22
    wph
    @151
    cL
    cc
    @149
    cL
    @150
    cB
    eqid
    iftruei
    #
    @27
    syl5eqel
    ifcld
    jca
    @18
    @76
    wa
    #
    @77
    wi
    @155
    @156
    wi
    vx
    cB
    @1
    @155
    @156
    vx
    @155
    vx
    nfv
    vx
    @145
    @152
    vx
    cB
    cG
    @73
    vx
    cB
    nfcv
    nffv
    nfeq1
    nfim
    @14
    @159
    @155
    @77
    @156
    @14
    @18
    @153
    @76
    @154
    @12
    cB
    @1
    eleq1
    @14
    @17
    @152
    cc
    @14
    @13
    @17
    @152
    wceq
    @14
    @13
    wa
    #
    @17
    cR
    @152
    @13
    @17
    cR
    wceq
    @14
    @139
    adantl
    @160
    @148
    cR
    @152
    wceq
    @12
    cB
    cA
    eqtr2
    @148
    @152
    cR
    @148
    cR
    @151
    iftrue
    eqcomd
    syl
    eqtrd
    @14
    @23
    wa
    #
    @17
    @16
    cL
    @152
    @23
    @17
    @16
    wceq
    @14
    @13
    cR
    @16
    iffalse
    adantl
    @14
    @16
    cL
    wceq
    @23
    @14
    cL
    @15
    iftrue
    adantr
    @161
    @152
    @151
    cL
    @161
    @148
    cR
    @151
    @161
    cB
    cA
    @23
    @14
    @79
    cB
    cA
    wne
    @12
    cA
    df-ne
    @12
    cB
    cA
    pm13.18
    sylan2br
    neneqd
    iffalsed
    @158
    syl6req
    3eqtrd
    pm2.61dan
    #
    eleq1d
    anbi12d
    @14
    @75
    @145
    @17
    @152
    @12
    cB
    cG
    fveq2
    @162
    eqeq12d
    imbi12d
    @78
    vtoclg1f
    sylc
    wph
    @148
    cR
    @151
    wph
    cB
    cA
    wph
    cA
    cB
    cncfiooicclem1.a
    cncfiooicclem1.altb
    gtned
    neneqd
    iffalsed
    @151
    cL
    wceq
    wph
    @158
    a1i
    3eqtrd
    wph
    cL
    @57
    cB
    climc
    co
    #
    @146
    wph
    cL
    @26
    @163
    cncfiooicclem1.l
    wph
    cF
    @57
    cB
    climc
    @141
    oveq1d
    eleqtrd
    wph
    cA
    cB
    cG
    cncfiooicclem1.a
    cncfiooicclem1.b
    cncfiooicclem1.altb
    @51
    limcicciooub
    eleqtrd
    eqeltrd
    wph
    @107
    @153
    @144
    @6
    @147
    wa
    wb
    @109
    @157
    @1
    cB
    cG
    @2
    @0
    @93
    @142
    cnplimc
    syl2anc
    mpbir2and
    adantr
    @131
    @143
    @9
    wceq
    wph
    @131
    @9
    @143
    @7
    cB
    @8
    fveq2
    eqcomd
    adantl
    eleqtrd
    jaodan
    sylan2
    jaodan
    syldan
    ralrimiva
    wph
    @2
    @1
    ctopon
    cfv
    wcel
    #
    @0
    cc
    ctopon
    cfv
    wcel
    #
    @5
    @6
    @11
    wa
    wb
    wph
    @165
    @107
    @164
    @0
    @93
    cnfldtopon
    #
    @109
    @1
    @0
    cc
    resttopon
    sylancr
    @166
    vy
    cG
    @2
    @0
    @1
    cc
    cncnp
    sylancl
    mpbir2and
    wph
    @107
    @90
    @4
    @3
    wceq
    @109
    @92
    @1
    cc
    @0
    @2
    @0
    @93
    @142
    @97
    cncfcn
    sylancl
    eleqtrrd
end
