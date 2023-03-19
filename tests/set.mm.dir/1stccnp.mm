include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "cn.mm"
include "cv.mm"
include "clm.mm"
include "wbr.mm"
include "wa.mm"
include "ccom.mm"
include "wi.mm"
include "wal.mm"
include "ctopon.mm"
include "jca.mm"
include "cnpf2.mm"
include "3expa.mm"
include "sylan.mm"
include "simprr.mm"
include "simplr.mm"
include "lmcnp.mm"
include "ex.mm"
include "alrimiv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "simprl.mm"
include "ccnv.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "ccl.mm"
include "wex.mm"
include "wfal.mm"
include "fal.mm"
include "19.29.mm"
include "difss.mm"
include "fss.mm"
include "sylancl.mm"
include "cuz.mm"
include "c1.mm"
include "nnuz.mm"
include "simplrr.mm"
include "1zzd.mm"
include "simplrl.mm"
include "lmcvg.mm"
include "r19.2uz.mm"
include "wfn.mm"
include "wceq.mm"
include "simprll.mm"
include "ffn.mm"
include "syl.mm"
include "fvco2.mm"
include "eleq1d.mm"
include "ffvelrnda.mm"
include "eldifad.mm"
include "wb.mm"
include "ad2antrr.mm"
include "elpreima.mm"
include "3syl.mm"
include "eldifbd.mm"
include "pm2.21d.mm"
include "sylbird.mm"
include "mpand.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mpd.mm"
include "expr.mm"
include "embantd.mm"
include "com23.mm"
include "impd.mm"
include "exlimdv.mm"
include "exp4b.mm"
include "impr.mm"
include "imp.mm"
include "mtoi.mm"
include "c1stc.mm"
include "cuni.mm"
include "toponuni.mm"
include "syl5sseq.mm"
include "eqid.mm"
include "1stcelcls.mm"
include "syl2anc.mm"
include "mtbird.mm"
include "ctop.mm"
include "topontop.mm"
include "eleqtrd.mm"
include "elcls.mm"
include "syl3anc.mm"
include "mtbid.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "toponss.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "df-ss.mm"
include "sylib.mm"
include "sseq1d.mm"
include "bitr4d.mm"
include "nne.mm"
include "inssdif0.mm"
include "bitr4i.mm"
include "syl6bbr.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "rexanali.mm"
include "syl6bb.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "iscnp.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem 1stccnp
  let wph: wff ph
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  assume 1stccnp.1: |- ( ph -> J e. 1stc )
  assume 1stccnp.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume 1stccnp.3: |- ( ph -> K e. ( TopOn ` Y ) )
  assume 1stccnp.4: |- ( ph -> P e. X )

  disjoint F f
  disjoint J f
  disjoint f ph
  disjoint K f
  disjoint X f
  disjoint Y f
  disjoint P f
  disjoint f j
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint F j
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint F k
  disjoint u v
  disjoint u x
  disjoint F u
  disjoint v x
  disjoint F v
  disjoint F x
  disjoint J j
  disjoint J k
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint K j
  disjoint K k
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint Y j
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y x
  disjoint P j
  disjoint P k
  disjoint P u
  disjoint P v
  assert |- ( ph -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. f ( ( f : NN --> X /\ f ( ~~>t ` J ) P ) -> ( F o. f ) ( ~~>t ` K ) ( F ` P ) ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cn
    cX
    vf
    cv
    #
    wf
    #
    @2
    cP
    cJ
    clm
    cfv
    wbr
    #
    wa
    #
    cF
    @2
    ccom
    #
    cP
    cF
    cfv
    #
    cK
    clm
    cfv
    wbr
    #
    wi
    #
    vf
    wal
    #
    wa
    #
    wph
    @0
    wa
    #
    @1
    @10
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    @0
    @1
    wph
    @13
    @14
    1stccnp.2
    1stccnp.3
    jca
    @13
    @14
    @0
    @1
    cP
    cF
    cJ
    cK
    cX
    cY
    cnpf2
    3expa
    sylan
    @12
    @9
    vf
    @12
    @5
    @8
    @12
    @5
    wa
    cP
    @2
    cF
    cJ
    cK
    @12
    @3
    @4
    simprr
    wph
    @0
    @5
    simplr
    lmcnp
    ex
    alrimiv
    jca
    wph
    @11
    wa
    #
    @0
    @1
    @7
    vu
    cv
    #
    wcel
    #
    cP
    vv
    cv
    #
    wcel
    #
    cF
    @18
    cima
    @16
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wph
    @1
    @10
    simprl
    #
    @15
    @23
    vu
    cK
    @15
    @16
    cK
    wcel
    #
    @17
    @22
    @15
    @26
    @17
    wa
    #
    wa
    #
    @22
    @19
    @18
    cX
    cF
    ccnv
    @16
    cima
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    wi
    vv
    cJ
    wral
    #
    wn
    #
    @28
    cP
    @30
    cJ
    ccl
    cfv
    cfv
    wcel
    #
    @33
    @28
    @35
    cn
    @30
    @2
    wf
    #
    @4
    wa
    #
    vf
    wex
    #
    @28
    @38
    wfal
    fal
    @15
    @27
    @38
    wfal
    wi
    #
    wph
    @1
    @10
    @27
    @39
    wi
    wph
    @1
    wa
    #
    @27
    @10
    @39
    @40
    @27
    @10
    @38
    wfal
    @10
    @38
    wa
    @9
    @37
    wa
    #
    vf
    wex
    @40
    @27
    wa
    #
    wfal
    @9
    @37
    vf
    19.29
    @42
    @41
    wfal
    vf
    @42
    @9
    @37
    wfal
    @42
    @37
    @9
    wfal
    @42
    @37
    @9
    wfal
    wi
    @42
    @37
    wa
    #
    @5
    @8
    wfal
    @43
    @3
    @4
    @43
    @36
    @30
    cX
    wss
    @3
    @42
    @36
    @4
    simprl
    cX
    @29
    difss
    #
    cn
    @30
    cX
    @2
    fss
    sylancl
    @42
    @36
    @4
    simprr
    jca
    @42
    @37
    @8
    wfal
    @42
    @37
    @8
    wa
    #
    wa
    #
    vk
    cv
    #
    @6
    cfv
    #
    @16
    wcel
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    cn
    wrex
    #
    wfal
    @46
    @7
    @16
    vj
    vk
    @6
    cK
    c1
    cn
    nnuz
    @40
    @26
    @17
    @45
    simplrr
    @46
    1zzd
    @42
    @37
    @8
    simprr
    @40
    @26
    @17
    @45
    simplrl
    lmcvg
    @50
    @49
    vk
    cn
    wrex
    @46
    wfal
    @49
    vj
    vk
    c1
    cn
    nnuz
    r19.2uz
    @46
    @49
    wfal
    vk
    cn
    @46
    @47
    cn
    wcel
    #
    wa
    #
    @49
    @47
    @2
    cfv
    #
    cF
    cfv
    #
    @16
    wcel
    #
    wfal
    @52
    @48
    @54
    @16
    @46
    @2
    cn
    wfn
    #
    @51
    @48
    @54
    wceq
    @46
    @36
    @56
    @42
    @36
    @4
    @8
    simprll
    #
    cn
    @30
    @2
    ffn
    syl
    cn
    cF
    @2
    @47
    fvco2
    sylan
    eleq1d
    @52
    @53
    cX
    wcel
    #
    @55
    wfal
    @52
    @53
    cX
    @29
    @46
    cn
    @30
    @47
    @2
    @57
    ffvelrnda
    #
    eldifad
    @52
    @58
    @55
    wa
    #
    @53
    @29
    wcel
    #
    wfal
    @52
    @1
    cF
    cX
    wfn
    @61
    @60
    wb
    @42
    @1
    @45
    @51
    wph
    @1
    @27
    simplr
    ad2antrr
    cX
    cY
    cF
    ffn
    cX
    @53
    @16
    cF
    elpreima
    3syl
    @52
    @61
    wfal
    @52
    @53
    cX
    @29
    @59
    eldifbd
    pm2.21d
    sylbird
    mpand
    sylbid
    rexlimdva
    syl5
    mpd
    expr
    embantd
    ex
    com23
    impd
    exlimdv
    syl5
    exp4b
    com23
    impr
    imp
    mtoi
    @28
    cJ
    c1stc
    wcel
    #
    @30
    cJ
    cuni
    #
    wss
    #
    @35
    @38
    wb
    wph
    @62
    @11
    @27
    1stccnp.1
    ad2antrr
    @28
    cX
    @30
    @63
    @44
    @28
    @13
    cX
    @63
    wceq
    wph
    @13
    @11
    @27
    1stccnp.2
    ad2antrr
    #
    cX
    cJ
    toponuni
    syl
    #
    syl5sseq
    #
    cP
    @30
    vf
    cJ
    @63
    @63
    eqid
    #
    1stcelcls
    syl2anc
    mtbird
    @28
    cJ
    ctop
    wcel
    #
    @64
    cP
    @63
    wcel
    @35
    @33
    wb
    @28
    @13
    @69
    @65
    cX
    cJ
    topontop
    syl
    @67
    @28
    cP
    cX
    @63
    wph
    cP
    cX
    wcel
    #
    @11
    @27
    1stccnp.4
    ad2antrr
    @66
    eleqtrd
    vv
    cP
    @30
    cJ
    @63
    @68
    elcls
    syl3anc
    mtbid
    @28
    @22
    @19
    @32
    wn
    #
    wa
    #
    vv
    cJ
    wrex
    @34
    @28
    @21
    @72
    vv
    cJ
    @28
    @18
    cJ
    wcel
    #
    wa
    #
    @20
    @71
    @19
    @74
    @20
    @18
    cX
    cin
    #
    @29
    wss
    #
    @71
    @74
    @20
    @18
    @29
    wss
    #
    @76
    @74
    cF
    wfun
    #
    @18
    cF
    cdm
    #
    wss
    @20
    @77
    wb
    @74
    @1
    @78
    @15
    @1
    @27
    @73
    @25
    ad2antrr
    #
    cX
    cY
    cF
    ffun
    syl
    @74
    @18
    cX
    @79
    @28
    @13
    @73
    @18
    cX
    wss
    #
    @65
    @18
    cJ
    cX
    toponss
    sylan
    #
    @74
    @1
    @79
    cX
    wceq
    @80
    cX
    cY
    cF
    fdm
    syl
    sseqtr4d
    @18
    @16
    cF
    funimass3
    syl2anc
    @74
    @75
    @18
    @29
    @74
    @81
    @75
    @18
    wceq
    @82
    @18
    cX
    df-ss
    sylib
    sseq1d
    bitr4d
    @71
    @31
    c0
    wceq
    @76
    @31
    c0
    nne
    @18
    cX
    @29
    inssdif0
    bitr4i
    syl6bbr
    anbi2d
    rexbidva
    @19
    @32
    vv
    cJ
    rexanali
    syl6bb
    mpbird
    expr
    ralrimiva
    wph
    @0
    @1
    @24
    wa
    wb
    #
    @11
    wph
    @13
    @14
    @70
    @83
    1stccnp.2
    1stccnp.3
    1stccnp.4
    vv
    vu
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp
    syl3anc
    adantr
    mpbir2and
    impbida
end
