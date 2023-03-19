include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "eqid.mm"
include "ellimc2.mm"
include "ccom.mm"
include "cbl.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "a1i.mm"
include "simplr.mm"
include "simpr.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "cxr.mm"
include "rpxr.mm"
include "adantl.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "ssrin.mm"
include "imass2.mm"
include "sstr2.mm"
include "3syl.mm"
include "com12.mm"
include "reximdv.mm"
include "syl5com.mm"
include "impr.mm"
include "rexlimiva.mm"
include "syl6.mm"
include "ralrimdva.mm"
include "r19.29r.mm"
include "ad3antrrr.mm"
include "rpxrd.mm"
include "ineq1.mm"
include "imaeq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "expr.mm"
include "syl2anc.mm"
include "rexlimdva.mm"
include "anim2d.mm"
include "syl9.mm"
include "impd.mm"
include "syl5.mm"
include "expd.mm"
include "expdimp.mm"
include "com23.mm"
include "impbid.mm"
include "wb.mm"
include "wfun.mm"
include "cdm.mm"
include "wf.mm"
include "ad2antrr.mm"
include "ffun.mm"
include "inss2.mm"
include "difss.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "syl5ss.mm"
include "funimass4.mm"
include "simplrr.mm"
include "sselda.mm"
include "elbl3.mm"
include "syl22anc.mm"
include "cnmetdval.mm"
include "breq1d.mm"
include "bitrd.mm"
include "simplrl.mm"
include "simpllr.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ralbidva.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitr2i.mm"
include "ralbii2.mm"
include "eldifsn.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "3bitr3g.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "pm5.32da.mm"

theorem ellimc3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  assume ellimc3.f: |- ( ph -> F : A --> CC )
  assume ellimc3.a: |- ( ph -> A C_ CC )
  assume ellimc3.b: |- ( ph -> B e. CC )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  disjoint ph u
  disjoint ph v
  disjoint F u
  disjoint F v
  assert |- ( ph -> ( C e. ( F limCC B ) <-> ( C e. CC /\ A. x e. RR+ E. y e. RR+ A. z e. A ( ( z =/= B /\ ( abs ` ( z - B ) ) < y ) -> ( abs ` ( ( F ` z ) - C ) ) < x ) ) ) )

  proof
    wph
    cC
    cF
    cB
    climc
    co
    wcel
    cC
    cc
    wcel
    #
    cC
    vu
    cv
    #
    wcel
    #
    cB
    vv
    cv
    #
    wcel
    #
    cF
    @3
    cA
    cB
    csn
    #
    cdif
    #
    cin
    #
    cima
    #
    @1
    wss
    #
    wa
    #
    vv
    ccnfld
    ctopn
    cfv
    #
    wrex
    #
    wi
    #
    vu
    @11
    wral
    #
    wa
    @0
    vz
    cv
    #
    cB
    wne
    #
    @15
    cB
    cmin
    co
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wa
    @15
    cF
    cfv
    #
    cC
    cmin
    co
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    crp
    wrex
    #
    vx
    crp
    wral
    #
    wa
    wph
    vv
    vu
    cA
    cB
    cC
    cF
    @11
    ellimc3.f
    ellimc3.a
    ellimc3.b
    @11
    eqid
    #
    ellimc2
    wph
    @0
    @14
    @27
    wph
    @0
    wa
    #
    @14
    cF
    cB
    @18
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    @6
    cin
    #
    cima
    #
    cC
    @22
    @31
    co
    #
    wss
    #
    vy
    crp
    wrex
    #
    vx
    crp
    wral
    #
    @27
    @29
    @14
    @38
    @29
    @14
    @37
    vx
    crp
    @29
    @22
    crp
    wcel
    #
    wa
    #
    @14
    @4
    @8
    @35
    wss
    #
    wa
    #
    vv
    @11
    wrex
    #
    @37
    @40
    @14
    cC
    @35
    wcel
    #
    @43
    @40
    @30
    cc
    cxmt
    cfv
    wcel
    #
    @0
    @39
    @44
    @45
    @40
    cnxmet
    a1i
    #
    wph
    @0
    @39
    simplr
    #
    @29
    @39
    simpr
    @30
    cC
    @22
    cc
    blcntr
    syl3anc
    @40
    @35
    @11
    wcel
    #
    @14
    @44
    @43
    wi
    #
    wi
    @40
    @45
    @0
    @22
    cxr
    wcel
    #
    @48
    @46
    @47
    @39
    @50
    @29
    @22
    rpxr
    adantl
    @30
    cC
    @22
    @11
    cc
    @11
    @28
    cnfldtopn
    #
    blopn
    syl3anc
    @13
    @49
    vu
    @35
    @11
    @1
    @35
    wceq
    #
    @2
    @44
    @12
    @43
    @1
    @35
    cC
    eleq2
    @52
    @10
    @42
    vv
    @11
    @52
    @9
    @41
    @4
    @1
    @35
    @8
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl
    mpid
    @42
    @37
    vv
    @11
    @3
    @11
    wcel
    #
    @4
    @41
    @37
    @53
    @4
    wa
    @32
    @3
    wss
    #
    vy
    crp
    wrex
    #
    @41
    @37
    @45
    @53
    @4
    @55
    cnxmet
    vy
    @3
    @30
    cB
    @11
    cc
    @51
    mopni2
    mp3an1
    @41
    @54
    @36
    vy
    crp
    @54
    @41
    @36
    @54
    @33
    @7
    wss
    @34
    @8
    wss
    @41
    @36
    wi
    @32
    @3
    @6
    ssrin
    @33
    @7
    cF
    imass2
    @34
    @8
    @35
    sstr2
    3syl
    com12
    reximdv
    syl5com
    impr
    rexlimiva
    syl6
    ralrimdva
    @29
    @38
    @13
    vu
    @11
    @29
    @1
    @11
    wcel
    #
    wa
    @2
    @38
    @12
    @29
    @56
    @2
    @38
    @12
    wi
    #
    @56
    @2
    wa
    @35
    @1
    wss
    #
    vx
    crp
    wrex
    #
    @29
    @57
    @45
    @56
    @2
    @59
    cnxmet
    vx
    @1
    @30
    cC
    @11
    cc
    @51
    mopni2
    mp3an1
    @29
    @59
    @38
    @12
    @59
    @38
    wa
    @58
    @37
    wa
    #
    vx
    crp
    wrex
    @29
    @12
    @58
    @37
    vx
    crp
    r19.29r
    @29
    @60
    @12
    vx
    crp
    @40
    @58
    @37
    @12
    @40
    @37
    @43
    @58
    @12
    @40
    @36
    @43
    vy
    crp
    @40
    @18
    crp
    wcel
    #
    wa
    #
    @32
    @11
    wcel
    #
    cB
    @32
    wcel
    #
    @36
    @43
    wi
    @62
    @45
    cB
    cc
    wcel
    #
    @18
    cxr
    wcel
    #
    @63
    @45
    @62
    cnxmet
    a1i
    #
    wph
    @65
    @0
    @39
    @61
    ellimc3.b
    ad3antrrr
    #
    @62
    @18
    @40
    @61
    simpr
    #
    rpxrd
    @30
    cB
    @18
    @11
    cc
    @51
    blopn
    syl3anc
    @62
    @45
    @65
    @61
    @64
    @67
    @68
    @69
    @30
    cB
    @18
    cc
    blcntr
    syl3anc
    @63
    @64
    @36
    @43
    @42
    @64
    @36
    wa
    vv
    @32
    @11
    @3
    @32
    wceq
    #
    @4
    @64
    @41
    @36
    @3
    @32
    cB
    eleq2
    @70
    @8
    @34
    @35
    @70
    @7
    @33
    cF
    @3
    @32
    @6
    ineq1
    imaeq2d
    sseq1d
    anbi12d
    rspcev
    expr
    syl2anc
    rexlimdva
    @58
    @42
    @10
    vv
    @11
    @58
    @41
    @9
    @4
    @41
    @58
    @9
    @8
    @35
    @1
    sstr2
    com12
    anim2d
    reximdv
    syl9
    impd
    rexlimdva
    syl5
    expd
    syl5
    expdimp
    com23
    ralrimdva
    impbid
    @29
    @37
    @26
    vx
    crp
    @40
    @36
    @25
    vy
    crp
    @29
    @39
    @61
    @36
    @25
    wb
    @29
    @39
    @61
    wa
    #
    wa
    #
    @36
    @20
    @35
    wcel
    #
    vz
    @33
    wral
    #
    @25
    @72
    cF
    wfun
    #
    @33
    cF
    cdm
    #
    wss
    @36
    @74
    wb
    @72
    cA
    cc
    cF
    wf
    #
    @75
    wph
    @77
    @0
    @71
    ellimc3.f
    ad2antrr
    #
    cA
    cc
    cF
    ffun
    syl
    @72
    @33
    @6
    @76
    @32
    @6
    inss2
    @72
    cA
    @6
    @76
    cA
    @5
    difss
    #
    @72
    @77
    @76
    cA
    wceq
    @78
    cA
    cc
    cF
    fdm
    syl
    syl5sseqr
    syl5ss
    vz
    @33
    @35
    cF
    funimass4
    syl2anc
    @72
    @15
    @32
    wcel
    #
    @73
    wi
    #
    vz
    @6
    wral
    @19
    @23
    wi
    #
    vz
    @6
    wral
    @74
    @25
    @72
    @81
    @82
    vz
    @6
    @72
    @15
    @6
    wcel
    #
    wa
    #
    @80
    @19
    @73
    @23
    @84
    @80
    @15
    cB
    @30
    co
    #
    @18
    clt
    wbr
    #
    @19
    @84
    @45
    @66
    @65
    @15
    cc
    wcel
    #
    @80
    @86
    wb
    @45
    @84
    cnxmet
    a1i
    #
    @84
    @18
    @29
    @39
    @61
    @83
    simplrr
    rpxrd
    wph
    @65
    @0
    @71
    @83
    ellimc3.b
    ad3antrrr
    #
    @72
    @6
    cc
    @15
    wph
    @6
    cc
    wss
    @0
    @71
    wph
    @6
    cA
    cc
    @79
    ellimc3.a
    syl5ss
    ad2antrr
    sselda
    #
    @15
    @30
    cB
    @18
    cc
    elbl3
    syl22anc
    @84
    @85
    @17
    @18
    clt
    @84
    @87
    @65
    @85
    @17
    wceq
    @90
    @89
    @15
    cB
    @30
    @30
    eqid
    #
    cnmetdval
    syl2anc
    breq1d
    bitrd
    @84
    @73
    @20
    cC
    @30
    co
    #
    @22
    clt
    wbr
    #
    @23
    @84
    @45
    @50
    @0
    @20
    cc
    wcel
    #
    @73
    @93
    wb
    @88
    @84
    @22
    @29
    @39
    @61
    @83
    simplrl
    rpxrd
    wph
    @0
    @71
    @83
    simpllr
    #
    @72
    @77
    @15
    cA
    wcel
    #
    @94
    @83
    @78
    @15
    cA
    @5
    eldifi
    cA
    cc
    @15
    cF
    ffvelrn
    syl2an
    #
    @20
    @30
    cC
    @22
    cc
    elbl3
    syl22anc
    @84
    @92
    @21
    @22
    clt
    @84
    @94
    @0
    @92
    @21
    wceq
    @97
    @95
    @20
    cC
    @30
    @91
    cnmetdval
    syl2anc
    breq1d
    bitrd
    imbi12d
    ralbidva
    @81
    @73
    vz
    @6
    @33
    @15
    @33
    wcel
    #
    @73
    wi
    @83
    @80
    wa
    #
    @73
    wi
    @83
    @81
    wi
    @98
    @99
    @73
    @98
    @80
    @83
    wa
    @99
    @15
    @32
    @6
    elin
    @80
    @83
    ancom
    bitri
    imbi1i
    @83
    @80
    @73
    impexp
    bitr2i
    ralbii2
    @82
    @24
    vz
    @6
    cA
    @96
    @16
    wa
    #
    @82
    wi
    @96
    @16
    @82
    wi
    #
    wi
    @83
    @82
    wi
    @96
    @24
    wi
    @96
    @16
    @82
    impexp
    @83
    @100
    @82
    @15
    cA
    cB
    eldifsn
    imbi1i
    @24
    @101
    @96
    @16
    @19
    @23
    impexp
    imbi2i
    3bitr4i
    ralbii2
    3bitr3g
    bitrd
    anassrs
    rexbidva
    ralbidva
    bitrd
    pm5.32da
    bitrd
end
