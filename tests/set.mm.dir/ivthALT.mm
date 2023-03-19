include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "cc.mm"
include "ccncf.mm"
include "cima.mm"
include "cfv.mm"
include "cioo.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfun.mm"
include "wf.mm"
include "simp31.mm"
include "cncff.mm"
include "syl.mm"
include "ffun.mm"
include "3ad2ant3.mm"
include "wral.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "cconn.mm"
include "cuni.mm"
include "cres.mm"
include "wfo.mm"
include "ccn.mm"
include "iccconn.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "cdm.mm"
include "wa.mm"
include "simpr1.mm"
include "anim2i.mm"
include "3impb.mm"
include "adantl.mm"
include "fdm.mm"
include "sseq2d.mm"
include "biimparc.mm"
include "jca.mm"
include "fores.mm"
include "wb.mm"
include "ctop.mm"
include "retop.mm"
include "simp332.mm"
include "uniretop.mm"
include "restuni.mm"
include "sylancr.mm"
include "foeq3.mm"
include "mpbid.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "simp331.mm"
include "ssid.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mpan2.mm"
include "3ad2ant2.mm"
include "eleqtrd.mm"
include "ctopon.mm"
include "simp32.mm"
include "resttopon.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "cvv.mm"
include "a1i.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "restabs.mm"
include "syl3anc.mm"
include "iccssre.mm"
include "rerest.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "df-ima.mm"
include "eqimss2i.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cnrest2.mm"
include "oveq2d.mm"
include "cnconn.mm"
include "reconn.mm"
include "wi.mm"
include "cxr.mm"
include "cle.mm"
include "simp11.mm"
include "rexrd.mm"
include "simp12.mm"
include "ltle.mm"
include "imp.mm"
include "3adantl3.mm"
include "lbicc2.mm"
include "funfvima2.mm"
include "sylc.mm"
include "ubicc2.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "mpd.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sseldd.mm"
include "fvelima.mm"
include "w3o.mm"
include "simpl1.mm"
include "simprr.mm"
include "wne.mm"
include "simp333.mm"
include "elioo2.mm"
include "simp2d.mm"
include "gtned.mm"
include "adantr.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "fveq2.mm"
include "nsyl.mm"
include "simp13.mm"
include "simp3d.mm"
include "ltned.mm"
include "simprl3.mm"
include "ecase13d.mm"
include "ex.mm"
include "jcad.mm"
include "3anass.mm"
include "syl6ibr.mm"
include "rexr.mm"
include "elicc3.mm"
include "syl2an.mm"
include "anbi1d.mm"
include "elioo1.mm"
include "3imtr4d.mm"
include "simpr.mm"
include "reximdv2.mm"

theorem ivthALT
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint F x
  disjoint U x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint D y
  disjoint F y
  disjoint U y
  assert |- ( ( ( A e. RR /\ B e. RR /\ U e. RR ) /\ A < B /\ ( ( A [,] B ) C_ D /\ D C_ CC /\ ( F e. ( D -cn-> CC ) /\ ( F " ( A [,] B ) ) C_ RR /\ U e. ( ( F ` A ) (,) ( F ` B ) ) ) ) ) -> E. x e. ( A (,) B ) ( F ` x ) = U )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cU
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cicc
    co
    #
    cD
    wss
    #
    cD
    cc
    wss
    #
    cF
    cD
    cc
    ccncf
    co
    #
    wcel
    #
    cF
    @5
    cima
    #
    cr
    wss
    #
    cU
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cioo
    co
    #
    wcel
    #
    w3a
    #
    w3a
    #
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    #
    cU
    wceq
    #
    vx
    @5
    wrex
    #
    @21
    vx
    cA
    cB
    cioo
    co
    #
    wrex
    @18
    cF
    wfun
    #
    cU
    @10
    wcel
    @22
    @17
    @3
    @24
    @4
    @17
    cD
    cc
    cF
    wf
    #
    @24
    @17
    @9
    @25
    @6
    @7
    @9
    @11
    @15
    simp31
    cD
    cc
    cF
    cncff
    #
    syl
    cD
    cc
    cF
    ffun
    #
    syl
    3ad2ant3
    @18
    @12
    @13
    cicc
    co
    #
    @10
    cU
    @18
    @19
    vy
    cv
    #
    cicc
    co
    #
    @10
    wss
    #
    vy
    @10
    wral
    vx
    @10
    wral
    #
    @28
    @10
    wss
    #
    @18
    cioo
    crn
    ctg
    cfv
    #
    @10
    crest
    co
    #
    cconn
    wcel
    #
    @32
    @18
    @34
    @5
    crest
    co
    #
    cconn
    wcel
    #
    @5
    @35
    cuni
    #
    cF
    @5
    cres
    #
    wfo
    #
    @40
    @37
    @35
    ccn
    co
    #
    wcel
    @36
    @3
    @4
    @38
    @17
    @0
    @1
    @38
    @2
    cA
    cB
    iccconn
    3adant3
    3ad2ant1
    @18
    @5
    @10
    @40
    wfo
    #
    @41
    @18
    @24
    @5
    cF
    cdm
    #
    wss
    #
    wa
    #
    @43
    @18
    @6
    @25
    wa
    #
    @46
    @17
    @3
    @47
    @4
    @6
    @7
    @16
    @47
    @7
    @16
    wa
    #
    @25
    @6
    @48
    @9
    @25
    @7
    @9
    @11
    @15
    simpr1
    @26
    syl
    anim2i
    3impb
    3ad2ant3
    @47
    @24
    @45
    @25
    @24
    @6
    @27
    adantl
    @25
    @45
    @6
    @25
    @44
    cD
    @5
    cD
    cc
    cF
    fdm
    sseq2d
    biimparc
    jca
    syl
    #
    @5
    cF
    fores
    syl
    @18
    @10
    @39
    wceq
    #
    @43
    @41
    wb
    @18
    @34
    ctop
    wcel
    @11
    @50
    retop
    @9
    @11
    @15
    @6
    @7
    @3
    @4
    simp332
    #
    @10
    @34
    cr
    uniretop
    restuni
    sylancr
    @10
    @39
    @5
    @40
    foeq3
    syl
    mpbid
    @18
    @40
    @37
    ccnfld
    ctopn
    cfv
    #
    @10
    crest
    co
    #
    ccn
    co
    #
    @42
    @18
    @40
    @37
    @52
    ccn
    co
    #
    wcel
    #
    @40
    @54
    wcel
    #
    @18
    @40
    @52
    cD
    crest
    co
    #
    @5
    crest
    co
    #
    @52
    ccn
    co
    #
    @55
    @18
    cF
    @58
    @52
    ccn
    co
    #
    wcel
    @5
    @58
    cuni
    #
    wss
    @40
    @60
    wcel
    @18
    cF
    @8
    @61
    @9
    @11
    @15
    @6
    @7
    @3
    @4
    simp331
    @17
    @3
    @8
    @61
    wceq
    #
    @4
    @7
    @6
    @63
    @16
    @7
    cc
    cc
    wss
    @63
    cc
    ssid
    cD
    cc
    @52
    @58
    @52
    @52
    eqid
    #
    @58
    eqid
    @52
    cc
    crest
    co
    #
    @52
    @52
    ctop
    wcel
    #
    @65
    @52
    wceq
    @52
    @64
    cnfldtop
    #
    @52
    ctop
    cc
    cc
    @52
    @52
    @64
    cnfldtopon
    #
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mpan2
    3ad2ant2
    3ad2ant3
    eleqtrd
    @18
    @5
    cD
    @62
    @3
    @4
    @6
    @7
    @16
    simp31
    #
    @18
    @58
    cD
    ctopon
    cfv
    wcel
    #
    cD
    @62
    wceq
    @18
    @52
    cc
    ctopon
    cfv
    wcel
    #
    @7
    @70
    @68
    @3
    @4
    @6
    @7
    @16
    simp32
    #
    cD
    @52
    cc
    resttopon
    sylancr
    cD
    @58
    toponuni
    syl
    sseqtrd
    @5
    cF
    @58
    @52
    @62
    @62
    eqid
    cnrest
    syl2anc
    @18
    @59
    @37
    @52
    ccn
    @18
    @59
    @52
    @5
    crest
    co
    #
    @37
    @18
    @66
    @6
    cD
    cvv
    wcel
    #
    @59
    @73
    wceq
    @66
    @18
    @67
    a1i
    @69
    @18
    @7
    cc
    cvv
    wcel
    @74
    @72
    cnex
    cD
    cc
    cvv
    ssexg
    sylancl
    @5
    cD
    @52
    ctop
    cvv
    restabs
    syl3anc
    @18
    @5
    cr
    wss
    #
    @73
    @37
    wceq
    @3
    @4
    @75
    @17
    @0
    @1
    @75
    @2
    cA
    cB
    iccssre
    3adant3
    3ad2ant1
    @5
    @34
    @52
    @64
    @34
    eqid
    #
    rerest
    syl
    eqtrd
    oveq1d
    eleqtrd
    @18
    @71
    @40
    crn
    #
    @10
    wss
    #
    @10
    cc
    wss
    @56
    @57
    wb
    @71
    @18
    @68
    a1i
    @78
    @18
    @10
    @77
    cF
    @5
    df-ima
    eqimss2i
    a1i
    @18
    @10
    cr
    cc
    @51
    ax-resscn
    syl6ss
    @10
    @40
    @37
    @52
    cc
    cnrest2
    syl3anc
    mpbid
    @18
    @53
    @35
    @37
    ccn
    @18
    @11
    @53
    @35
    wceq
    @51
    @10
    @34
    @52
    @64
    @76
    rerest
    syl
    oveq2d
    eleqtrd
    @40
    @37
    @35
    @5
    @39
    @39
    eqid
    cnconn
    syl3anc
    @17
    @3
    @36
    @32
    wb
    #
    @4
    @16
    @6
    @79
    @7
    @11
    @9
    @79
    @15
    vx
    vy
    @10
    reconn
    3ad2ant2
    3ad2ant3
    3ad2ant3
    mpbid
    @18
    @12
    @10
    wcel
    #
    @13
    @10
    wcel
    #
    @32
    @33
    wi
    @18
    @46
    cA
    @5
    wcel
    #
    @80
    @49
    @18
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
    @82
    @18
    cA
    @0
    @1
    @2
    @4
    @17
    simp11
    rexrd
    #
    @18
    cB
    @0
    @1
    @2
    @4
    @17
    simp12
    rexrd
    #
    @3
    @4
    @85
    @17
    @0
    @1
    @4
    @85
    @2
    @0
    @1
    wa
    @4
    @85
    cA
    cB
    ltle
    imp
    3adantl3
    3adant3
    #
    cA
    cB
    lbicc2
    syl3anc
    @5
    cA
    cF
    funfvima2
    sylc
    #
    @18
    @46
    cB
    @5
    wcel
    #
    @81
    @49
    @18
    @83
    @84
    @85
    @90
    @86
    @87
    @88
    cA
    cB
    ubicc2
    syl3anc
    @5
    cB
    cF
    funfvima2
    sylc
    #
    @31
    @33
    @12
    @29
    cicc
    co
    #
    @10
    wss
    vx
    vy
    @12
    @13
    @10
    @10
    @19
    @12
    wceq
    @30
    @92
    @10
    @19
    @12
    @29
    cicc
    oveq1
    sseq1d
    @29
    @13
    wceq
    @92
    @28
    @10
    @29
    @13
    @12
    cicc
    oveq2
    sseq1d
    rspc2v
    syl2anc
    mpd
    @17
    @3
    cU
    @28
    wcel
    #
    @4
    @16
    @6
    @93
    @7
    @15
    @9
    @93
    @11
    @14
    @28
    cU
    @12
    @13
    ioossicc
    sseli
    3ad2ant3
    3ad2ant3
    3ad2ant3
    sseldd
    vx
    cU
    @5
    cF
    fvelima
    syl2anc
    @18
    @21
    @21
    vx
    @5
    @23
    @18
    @19
    @5
    wcel
    #
    @21
    wa
    #
    @19
    @23
    wcel
    #
    @21
    @18
    @19
    cxr
    wcel
    #
    @85
    @19
    cA
    wceq
    #
    cA
    @19
    clt
    wbr
    #
    @19
    cB
    clt
    wbr
    #
    wa
    #
    @19
    cB
    wceq
    #
    w3o
    #
    w3a
    #
    @21
    wa
    #
    @97
    @99
    @100
    w3a
    #
    @95
    @96
    @18
    @105
    @97
    @101
    wa
    @106
    @18
    @105
    @97
    @101
    @105
    @97
    wi
    @18
    @97
    @85
    @103
    @21
    simpl1
    a1i
    @18
    @105
    @101
    @18
    @105
    wa
    #
    @101
    @98
    @102
    @107
    @20
    @12
    wceq
    @98
    @107
    @20
    @12
    @107
    @20
    cU
    @12
    @18
    @104
    @21
    simprr
    #
    @18
    cU
    @12
    wne
    @105
    @18
    @12
    cU
    @18
    @10
    cr
    @12
    @51
    @89
    sseldd
    #
    @18
    @2
    @12
    cU
    clt
    wbr
    #
    cU
    @13
    clt
    wbr
    #
    @18
    @15
    @2
    @110
    @111
    w3a
    #
    @9
    @11
    @15
    @6
    @7
    @3
    @4
    simp333
    @18
    @12
    cxr
    wcel
    @13
    cxr
    wcel
    @15
    @112
    wb
    @18
    @12
    @109
    rexrd
    @18
    @13
    @18
    @10
    cr
    @13
    @51
    @91
    sseldd
    rexrd
    @12
    @13
    cU
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    gtned
    adantr
    eqnetrd
    neneqd
    @19
    cA
    cF
    fveq2
    nsyl
    @107
    @20
    @13
    wceq
    @102
    @107
    @20
    @13
    @107
    @20
    cU
    @13
    @108
    @18
    cU
    @13
    wne
    @105
    @18
    cU
    @13
    @0
    @1
    @2
    @4
    @17
    simp13
    @18
    @2
    @110
    @111
    @113
    simp3d
    ltned
    adantr
    eqnetrd
    neneqd
    @19
    cB
    cF
    fveq2
    nsyl
    @97
    @85
    @103
    @21
    @18
    simprl3
    ecase13d
    ex
    jcad
    @97
    @99
    @100
    3anass
    syl6ibr
    @18
    @94
    @104
    @21
    @3
    @4
    @94
    @104
    wb
    #
    @17
    @0
    @1
    @114
    @2
    @0
    @83
    @84
    @114
    @1
    cA
    rexr
    #
    cB
    rexr
    #
    cA
    cB
    @19
    elicc3
    syl2an
    3adant3
    3ad2ant1
    anbi1d
    @3
    @4
    @96
    @106
    wb
    #
    @17
    @0
    @1
    @117
    @2
    @0
    @83
    @84
    @117
    @1
    @115
    @116
    cA
    cB
    @19
    elioo1
    syl2an
    3adant3
    3ad2ant1
    3imtr4d
    @95
    @21
    wi
    @18
    @94
    @21
    simpr
    a1i
    jcad
    reximdv2
    mpd
end
