include "cioo.mm"
include "co.mm"
include "cr.mm"
include "cdv.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "cc.mm"
include "wf.mm"
include "dvf.mm"
include "a1i.mm"
include "ffun.mm"
include "syl.mm"
include "cicc.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wss.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "ioossre.mm"
include "ccncf.mm"
include "wcel.mm"
include "cncff.mm"
include "ftc1lem2.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvbssntr.mm"
include "iccntr.mm"
include "sseqtrd.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "crest.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "ctop.mm"
include "retop.mm"
include "eqeltrri.mm"
include "adantr.mm"
include "iooretop.mm"
include "eleqtri.mm"
include "ioossicc.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtri.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "simpr.mm"
include "sseldd.mm"
include "wne.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ffvelrnda.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "cmopn.mm"
include "ccnp.mm"
include "cnxmet.mm"
include "sstri.mm"
include "xmetres2.mm"
include "mp2an.mm"
include "ccn.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "syl6eleq.mm"
include "ctopon.mm"
include "resttopon.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cncnpi.mm"
include "syl2an.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "oveq1i.mm"
include "fveq1i.mm"
include "metcnpi2.mm"
include "simpllr.mm"
include "ovresd.mm"
include "elioore.mm"
include "recnd.mm"
include "adantl.mm"
include "sseli.mm"
include "ad3antlr.mm"
include "cnmetdval.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "ad2antrr.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "simprll.mm"
include "eldifsni.mm"
include "wo.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "ad2ant2r.mm"
include "lttri2d.mm"
include "biimpa.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antlr.mm"
include "ad4antr.mm"
include "eldifi.mm"
include "ffvelrnd.mm"
include "sylan2.mm"
include "ad3antrrr.mm"
include "ad4antlr.mm"
include "ltne.mm"
include "necomd.mm"
include "sylan.mm"
include "div2subd.mm"
include "fveq2d.mm"
include "cle.mm"
include "cibl.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprlr.mm"
include "rspccva.mm"
include "simprr.mm"
include "cc0.mm"
include "subidd.mm"
include "abs00bd.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "ftc1cnnclem.mm"
include "jaodan.mm"
include "syldan.mm"
include "mpdan.mm"
include "expr.mm"
include "adantld.mm"
include "ralrimdva.mm"
include "sylbid.mm"
include "anassrs.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "syl6ss.mm"
include "dvlem.mm"
include "fmptd.mm"
include "ellimc3.mm"
include "mpbir2and.mm"
include "wb.mm"
include "eldv.mm"
include "vex.mm"
include "fvex.mm"
include "breldm.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "ffn.mm"
include "funbrfv.mm"
include "sylc.mm"
include "eqfnfvd.mm"

theorem ftc1cnnc
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vc: setvar c
  assume ftc1cnnc.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1cnnc.a: |- ( ph -> A e. RR )
  assume ftc1cnnc.b: |- ( ph -> B e. RR )
  assume ftc1cnnc.le: |- ( ph -> A <_ B )
  assume ftc1cnnc.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume ftc1cnnc.i: |- ( ph -> F e. L^1 )

  disjoint t x
  disjoint A x
  disjoint A t
  disjoint B x
  disjoint B t
  disjoint F x
  disjoint F t
  disjoint ph x
  disjoint ph t
  disjoint x y
  disjoint x z
  disjoint s x
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint y z
  disjoint t y
  disjoint s y
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint A y
  disjoint t z
  disjoint s z
  disjoint u z
  disjoint v z
  disjoint w z
  disjoint A z
  disjoint s t
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint A s
  disjoint u v
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint F y
  disjoint F z
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint ph y
  disjoint ph z
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint G y
  disjoint G z
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint c t
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint A c
  disjoint B c
  disjoint F c
  disjoint c ph
  disjoint G c
  assert |- ( ph -> ( RR _D G ) = F )

  proof
    wph
    vc
    cA
    cB
    cioo
    co
    #
    cr
    cG
    cdv
    co
    #
    cF
    wph
    @1
    wfun
    #
    @1
    cdm
    #
    @0
    wceq
    @1
    @0
    wfn
    wph
    @3
    cc
    @1
    wf
    #
    @2
    @4
    wph
    cG
    dvf
    a1i
    @3
    cc
    @1
    ffun
    syl
    #
    wph
    @3
    @0
    wph
    @3
    cA
    cB
    cicc
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    @0
    wph
    @6
    cr
    cG
    @7
    ccnfld
    ctopn
    cfv
    #
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    wph
    vx
    vt
    cA
    cB
    @0
    cF
    cG
    ftc1cnnc.g
    ftc1cnnc.a
    ftc1cnnc.b
    ftc1cnnc.le
    @0
    @0
    wss
    wph
    @0
    ssid
    a1i
    @0
    cr
    wss
    wph
    cA
    cB
    ioossre
    #
    a1i
    ftc1cnnc.i
    wph
    cF
    @0
    cc
    ccncf
    co
    #
    wcel
    #
    @0
    cc
    cF
    wf
    #
    ftc1cnnc.f
    @0
    cc
    cF
    cncff
    syl
    #
    ftc1lem2
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @6
    cr
    wss
    #
    ftc1cnnc.a
    ftc1cnnc.b
    cA
    cB
    iccssre
    syl2anc
    #
    @9
    @9
    eqid
    #
    tgioo2
    #
    @21
    dvbssntr
    wph
    @17
    @18
    @8
    @0
    wceq
    ftc1cnnc.a
    ftc1cnnc.b
    cA
    cB
    iccntr
    syl2anc
    sseqtrd
    wph
    vc
    @0
    @3
    wph
    vc
    cv
    #
    @0
    wcel
    #
    @23
    @3
    wcel
    #
    wph
    @24
    wa
    #
    @23
    @23
    cF
    cfv
    #
    @1
    wbr
    #
    @25
    @26
    @28
    @23
    @6
    @9
    cr
    crest
    co
    #
    cnt
    cfv
    cfv
    #
    wcel
    #
    @27
    vs
    @6
    @23
    csn
    #
    cdif
    #
    vs
    cv
    #
    cG
    cfv
    #
    @23
    cG
    cfv
    #
    cmin
    co
    #
    @34
    @23
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @23
    climc
    co
    wcel
    #
    @26
    @0
    @30
    @23
    @26
    @29
    ctop
    wcel
    #
    @19
    @0
    @29
    wcel
    #
    @0
    @6
    wss
    #
    @0
    @30
    wss
    @42
    @26
    @7
    @29
    ctop
    @22
    retop
    eqeltrri
    a1i
    wph
    @19
    @24
    @20
    adantr
    @43
    @26
    @0
    @7
    @29
    cA
    cB
    iooretop
    @22
    eleqtri
    a1i
    @44
    @26
    cA
    cB
    ioossicc
    #
    a1i
    @6
    @29
    @0
    cr
    cr
    @7
    cuni
    @29
    cuni
    uniretop
    @7
    @29
    @22
    unieqi
    eqtri
    ssntr
    syl22anc
    wph
    @24
    simpr
    sseldd
    @26
    @41
    @27
    cc
    wcel
    #
    vz
    cv
    #
    @23
    wne
    #
    @47
    @23
    cmin
    co
    #
    cabs
    cfv
    vv
    cv
    #
    clt
    wbr
    #
    wa
    @47
    @40
    cfv
    #
    @27
    cmin
    co
    #
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    @33
    wral
    #
    vv
    crp
    wrex
    #
    vw
    crp
    wral
    wph
    @0
    cc
    @23
    cF
    @15
    ffvelrnda
    #
    @26
    @59
    vw
    crp
    @26
    @55
    crp
    wcel
    #
    wa
    #
    vu
    cv
    #
    @23
    cabs
    cmin
    ccom
    #
    @0
    @0
    cxp
    cres
    #
    co
    #
    @50
    clt
    wbr
    #
    @63
    cF
    cfv
    #
    @27
    @64
    co
    #
    @55
    clt
    wbr
    #
    wi
    #
    vu
    @0
    wral
    #
    vv
    crp
    wrex
    #
    @59
    @62
    @65
    @0
    cxmt
    cfv
    wcel
    #
    @64
    cc
    cxmt
    cfv
    wcel
    #
    cF
    @23
    @65
    cmopn
    cfv
    #
    @9
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @61
    @73
    @74
    @62
    @75
    @0
    cc
    wss
    #
    @74
    cnxmet
    @0
    cr
    cc
    @11
    ax-resscn
    sstri
    #
    @64
    @0
    cc
    xmetres2
    mp2an
    a1i
    @75
    @62
    cnxmet
    a1i
    @26
    @79
    @61
    @26
    cF
    @23
    @9
    @0
    crest
    co
    #
    @9
    ccnp
    co
    #
    cfv
    #
    @78
    wph
    cF
    @82
    @9
    ccn
    co
    #
    wcel
    @23
    @82
    cuni
    #
    wcel
    #
    cF
    @84
    wcel
    @24
    wph
    cF
    @12
    @85
    ftc1cnnc.f
    @80
    cc
    cc
    wss
    @12
    @85
    wceq
    @81
    cc
    ssid
    @0
    cc
    @9
    @82
    @9
    @21
    @82
    eqid
    @9
    cc
    crest
    co
    #
    @9
    @9
    ctop
    wcel
    @88
    @9
    wceq
    @9
    @21
    cnfldtop
    @9
    ctop
    cc
    cc
    @9
    @9
    @21
    cnfldtopon
    #
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    syl6eleq
    @24
    @87
    @0
    @86
    @23
    @0
    @82
    @9
    cc
    ctopon
    cfv
    wcel
    @80
    @82
    @0
    ctopon
    cfv
    wcel
    @89
    @81
    @0
    @9
    cc
    resttopon
    mp2an
    toponunii
    eleq2i
    biimpi
    @23
    cF
    @82
    @9
    @86
    @86
    eqid
    cncnpi
    syl2an
    @23
    @83
    @77
    @82
    @76
    @9
    ccnp
    @75
    @80
    @82
    @76
    wceq
    cnxmet
    @81
    @64
    @65
    @9
    @76
    cc
    @0
    @65
    eqid
    @9
    @21
    cnfldtopn
    #
    @76
    eqid
    #
    metrest
    mp2an
    oveq1i
    fveq1i
    syl6eleq
    adantr
    @26
    @61
    simpr
    vv
    vu
    @55
    @65
    @64
    @23
    cF
    @76
    @9
    @0
    cc
    @91
    @90
    metcnpi2
    syl22anc
    @62
    @72
    @58
    vv
    crp
    @26
    @61
    @50
    crp
    wcel
    #
    @72
    @58
    wi
    @26
    @61
    @92
    wa
    #
    wa
    #
    @72
    @63
    @23
    cmin
    co
    #
    cabs
    cfv
    #
    @50
    clt
    wbr
    #
    @68
    @27
    cmin
    co
    #
    cabs
    cfv
    #
    @55
    clt
    wbr
    #
    wi
    #
    vu
    @0
    wral
    #
    @58
    @94
    @71
    @101
    vu
    @0
    @94
    @63
    @0
    wcel
    #
    wa
    #
    @67
    @97
    @70
    @100
    @104
    @66
    @96
    @50
    clt
    @104
    @66
    @63
    @23
    @64
    co
    #
    @96
    @104
    @63
    @23
    @64
    @0
    @94
    @103
    simpr
    wph
    @24
    @93
    @103
    simpllr
    ovresd
    @104
    @63
    cc
    wcel
    #
    @23
    cc
    wcel
    #
    @105
    @96
    wceq
    @103
    @106
    @94
    @103
    @63
    @63
    cA
    cB
    elioore
    recnd
    adantl
    @24
    @107
    wph
    @93
    @103
    @0
    cc
    @23
    @81
    sseli
    #
    ad3antlr
    @63
    @23
    @64
    @64
    eqid
    #
    cnmetdval
    syl2anc
    eqtrd
    breq1d
    @104
    @69
    @99
    @55
    clt
    @104
    @68
    cc
    wcel
    @46
    @69
    @99
    wceq
    @94
    @0
    cc
    @63
    cF
    wph
    @14
    @24
    @93
    @15
    ad2antrr
    ffvelrnda
    @26
    @46
    @93
    @103
    @60
    ad2antrr
    @68
    @27
    @64
    @109
    cnmetdval
    syl2anc
    breq1d
    imbi12d
    ralbidva
    @94
    @102
    @57
    vz
    @33
    @94
    @47
    @33
    wcel
    #
    @102
    @57
    @94
    @110
    @102
    wa
    #
    wa
    @51
    @56
    @48
    @94
    @111
    @51
    @56
    @94
    @111
    @51
    wa
    #
    wa
    #
    @48
    @56
    @113
    @110
    @48
    @94
    @110
    @102
    @51
    simprll
    #
    @47
    @6
    @23
    eldifsni
    syl
    @113
    @48
    @47
    @23
    clt
    wbr
    #
    @23
    @47
    clt
    wbr
    #
    wo
    #
    @56
    @113
    @48
    @117
    @113
    @47
    @23
    @26
    @111
    @47
    cr
    wcel
    #
    @93
    @51
    wph
    @110
    @118
    @24
    @102
    wph
    @33
    cr
    @47
    wph
    @6
    cr
    @32
    @20
    ssdifssd
    sselda
    ad2ant2r
    ad2ant2r
    #
    @24
    @23
    cr
    wcel
    wph
    @93
    @112
    @23
    cA
    cB
    elioore
    #
    ad3antlr
    lttri2d
    biimpa
    @113
    @115
    @56
    @116
    @113
    @115
    wa
    #
    @54
    @36
    @47
    cG
    cfv
    #
    cmin
    co
    @23
    @47
    cmin
    co
    cdiv
    co
    #
    @27
    cmin
    co
    #
    cabs
    cfv
    @55
    clt
    @121
    @53
    @124
    cabs
    @121
    @52
    @123
    @27
    cmin
    @121
    @52
    @122
    @36
    cmin
    co
    #
    @49
    cdiv
    co
    #
    @123
    @112
    @52
    @126
    wceq
    #
    @94
    @115
    @110
    @127
    @102
    @51
    vs
    @47
    @39
    @126
    @33
    @40
    vs
    vz
    weq
    #
    @37
    @125
    @38
    @49
    cdiv
    @128
    @35
    @122
    @36
    cmin
    @34
    @47
    cG
    fveq2
    oveq1d
    @34
    @47
    @23
    cmin
    oveq1
    oveq12d
    @40
    eqid
    #
    @125
    @49
    cdiv
    ovex
    fvmpt
    #
    ad2antrr
    ad2antlr
    @121
    @122
    @36
    @47
    @23
    @121
    @6
    cc
    @47
    cG
    wph
    @6
    cc
    cG
    wf
    #
    @24
    @93
    @112
    @115
    @16
    ad4antr
    @112
    @47
    @6
    wcel
    #
    @94
    @115
    @110
    @132
    @102
    @51
    @47
    @6
    @32
    eldifi
    #
    ad2antrr
    ad2antlr
    ffvelrnd
    @26
    @36
    cc
    wcel
    #
    @93
    @112
    @115
    @24
    wph
    @23
    @6
    wcel
    #
    @134
    @0
    @6
    @23
    @45
    sseli
    #
    wph
    @6
    cc
    @23
    cG
    @16
    ffvelrnda
    sylan2
    ad3antrrr
    @121
    @47
    @113
    @118
    @115
    @119
    adantr
    recnd
    @24
    @107
    wph
    @93
    @112
    @115
    @108
    ad4antlr
    @113
    @118
    @115
    @48
    @119
    @118
    @115
    wa
    @23
    @47
    @47
    @23
    ltne
    necomd
    sylan
    div2subd
    eqtrd
    oveq1d
    fveq2d
    @113
    vx
    vy
    vs
    vt
    cA
    cB
    @50
    @55
    cF
    cG
    @40
    @47
    @23
    vc
    ftc1cnnc.g
    wph
    @17
    @24
    @93
    @112
    ftc1cnnc.a
    ad3antrrr
    #
    wph
    @18
    @24
    @93
    @112
    ftc1cnnc.b
    ad3antrrr
    #
    wph
    cA
    cB
    cle
    wbr
    @24
    @93
    @112
    ftc1cnnc.le
    ad3antrrr
    #
    wph
    @13
    @24
    @93
    @112
    ftc1cnnc.f
    ad3antrrr
    #
    wph
    cF
    cibl
    wcel
    @24
    @93
    @112
    ftc1cnnc.i
    ad3antrrr
    #
    wph
    @24
    @93
    @112
    simpllr
    #
    @129
    @26
    @61
    @92
    @112
    simplrl
    #
    @26
    @61
    @92
    @112
    simplrr
    #
    @113
    @102
    vy
    cv
    #
    @0
    wcel
    @145
    @23
    cmin
    co
    #
    cabs
    cfv
    #
    @50
    clt
    wbr
    #
    @145
    cF
    cfv
    #
    @27
    cmin
    co
    #
    cabs
    cfv
    #
    @55
    clt
    wbr
    #
    wi
    #
    @94
    @110
    @102
    @51
    simprlr
    @101
    @153
    vu
    @145
    @0
    vu
    vy
    weq
    #
    @97
    @148
    @100
    @152
    @154
    @96
    @147
    @50
    clt
    @154
    @95
    @146
    cabs
    @63
    @145
    @23
    cmin
    oveq1
    fveq2d
    breq1d
    @154
    @99
    @151
    @55
    clt
    @154
    @98
    @150
    cabs
    @154
    @68
    @149
    @27
    cmin
    @63
    @145
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspccva
    sylan
    #
    @113
    @110
    @132
    @114
    @133
    syl
    #
    @94
    @111
    @51
    simprr
    #
    @24
    @135
    wph
    @93
    @112
    @136
    ad3antlr
    #
    @113
    @23
    @23
    cmin
    co
    #
    cabs
    cfv
    #
    cc0
    @50
    clt
    @24
    @160
    cc0
    wceq
    wph
    @93
    @112
    @24
    @159
    @24
    @23
    @24
    @23
    @120
    recnd
    subidd
    abs00bd
    ad3antlr
    @113
    @50
    @144
    rpgt0d
    eqbrtrd
    #
    ftc1cnnclem
    eqbrtrd
    @113
    @116
    wa
    @54
    @126
    @27
    cmin
    co
    #
    cabs
    cfv
    #
    @55
    clt
    @112
    @54
    @163
    wceq
    #
    @94
    @116
    @110
    @164
    @102
    @51
    @110
    @53
    @162
    cabs
    @110
    @52
    @126
    @27
    cmin
    @130
    oveq1d
    fveq2d
    ad2antrr
    ad2antlr
    @113
    vx
    vy
    vs
    vt
    cA
    cB
    @50
    @55
    cF
    cG
    @40
    @23
    @47
    vc
    ftc1cnnc.g
    @137
    @138
    @139
    @140
    @141
    @142
    @129
    @143
    @144
    @155
    @158
    @161
    @156
    @157
    ftc1cnnclem
    eqbrtrd
    jaodan
    syldan
    mpdan
    expr
    adantld
    expr
    ralrimdva
    sylbid
    anassrs
    reximdva
    mpd
    ralrimiva
    @26
    vw
    vv
    vz
    @33
    @23
    @27
    @40
    @26
    vs
    @33
    @39
    cc
    @40
    @26
    @34
    @23
    @6
    cG
    wph
    @131
    @24
    @16
    adantr
    wph
    @6
    cc
    wss
    @24
    wph
    @6
    cr
    cc
    @20
    ax-resscn
    syl6ss
    #
    adantr
    @24
    @135
    wph
    @136
    adantl
    dvlem
    @129
    fmptd
    wph
    @33
    cc
    wss
    @24
    wph
    @6
    cc
    @32
    @165
    ssdifssd
    adantr
    @24
    @107
    wph
    @108
    adantl
    ellimc3
    mpbir2and
    wph
    @28
    @31
    @41
    wa
    wb
    @24
    wph
    vs
    @6
    @23
    @27
    cr
    @29
    cG
    @40
    @9
    @29
    eqid
    @21
    @129
    @10
    @16
    @20
    eldv
    adantr
    mpbir2and
    #
    @23
    @27
    @1
    vc
    vex
    @23
    cF
    fvex
    breldm
    syl
    ex
    ssrdv
    eqssd
    @1
    @0
    df-fn
    sylanbrc
    wph
    @14
    cF
    @0
    wfn
    @15
    @0
    cc
    cF
    ffn
    syl
    @26
    @2
    @28
    @23
    @1
    cfv
    @27
    wceq
    wph
    @2
    @24
    @5
    adantr
    @166
    @23
    @27
    @1
    funbrfv
    sylc
    eqfnfvd
end
