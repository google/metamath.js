include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "cioo.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wf.mm"
include "caddc.mm"
include "cres.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cmul.mm"
include "ccos.mm"
include "cmin.mm"
include "cexp.mm"
include "cmpt.mm"
include "wa.mm"
include "wi.mm"
include "cicc.mm"
include "cpi.mm"
include "cneg.mm"
include "ioossicc.mm"
include "syl5ss.mm"
include "cc0.mm"
include "wcel.mm"
include "sseli.mm"
include "nsyl.mm"
include "fourierdlem57.mm"
include "simpli.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "crp.mm"
include "eqid.mm"
include "ltled.mm"
include "csn.mm"
include "cdif.mm"
include "ccncf.mm"
include "wne.mm"
include "2re.mm"
include "a1i.mm"
include "iccssred.mm"
include "sselda.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "remulcld.mm"
include "2cnd.mm"
include "recnd.mm"
include "2ne0.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "fourierdlem44.mm"
include "syl2anc.mm"
include "mulne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "fmptd.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "difss.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "syl6ss.mm"
include "ssid.mm"
include "constcncfg.mm"
include "sincn.mm"
include "idcncfg.mm"
include "difssd.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "divcncf.mm"
include "cncfmpt1f.mm"
include "mulcncf.mm"
include "cncficcgt0.mm"
include "w3a.mm"
include "c1.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "adantr.mm"
include "elioore.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "3ad2antl1.mm"
include "cxr.mm"
include "rexrd.mm"
include "clt.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd2dd.mm"
include "iooltub.mm"
include "eliood.mm"
include "fourierdlem28.mm"
include "0red.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "crn.mm"
include "ctg.mm"
include "iooretop.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "dvmptconst.mm"
include "dvmptsub.mm"
include "subid1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "3ad2ant1.mm"
include "halfcld.mm"
include "sincld.mm"
include "mulcld.mm"
include "1re.mm"
include "remulcli.mm"
include "1red.mm"
include "abscld.mm"
include "jca.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "absmuld.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "abssinbd.mm"
include "lemul2ad.mm"
include "syl5eqbr.mm"
include "eqbrtrd.mm"
include "abscosbd.mm"
include "3syl.mm"
include "abs2dif2d.mm"
include "leadd1dd.mm"
include "letrd.mm"
include "simpri.mm"
include "coscld.mm"
include "simp2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "cbvralv.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simplr.mm"
include "sseldi.mm"
include "adantlr.mm"
include "rspa.mm"
include "ex.mm"
include "ralrimi.mm"
include "sylan2b.mm"
include "3adant2.mm"
include "dvdivbd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfdm.mm"
include "raleqf.mm"
include "rexbidv.mm"
include "fveq1d.mm"
include "rexralbidv.mm"

theorem fourierdlem68
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cO: class O
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem68.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem68.xre: |- ( ph -> X e. RR )
  assume fourierdlem68.a: |- ( ph -> A e. RR )
  assume fourierdlem68.b: |- ( ph -> B e. RR )
  assume fourierdlem68.altb: |- ( ph -> A < B )
  assume fourierdlem68.ab: |- ( ph -> ( A [,] B ) C_ ( -u _pi [,] _pi ) )
  assume fourierdlem68.n0: |- ( ph -> -. 0 e. ( A [,] B ) )
  assume fourierdlem68.fdv: |- ( ph -> ( RR _D ( F |` ( ( X + A ) (,) ( X + B ) ) ) ) : ( ( X + A ) (,) ( X + B ) ) --> RR )
  assume fourierdlem68.d: |- ( ph -> D e. RR )
  assume fourierdlem68.fbd: |- ( ( ph /\ t e. ( ( X + A ) (,) ( X + B ) ) ) -> ( abs ` ( F ` t ) ) <_ D )
  assume fourierdlem68.e: |- ( ph -> E e. RR )
  assume fourierdlem68.fdvbd: |- ( ( ph /\ t e. ( ( X + A ) (,) ( X + B ) ) ) -> ( abs ` ( ( RR _D ( F |` ( ( X + A ) (,) ( X + B ) ) ) ) ` t ) ) <_ E )
  assume fourierdlem68.c: |- ( ph -> C e. RR )
  assume fourierdlem68.o: |- O = ( s e. ( A (,) B ) |-> ( ( ( F ` ( X + s ) ) - C ) / ( 2 x. ( sin ` ( s / 2 ) ) ) ) )

  disjoint A b
  disjoint A s
  disjoint b s
  disjoint A t
  disjoint s t
  disjoint B b
  disjoint B s
  disjoint B t
  disjoint C b
  disjoint C s
  disjoint D b
  disjoint D s
  disjoint D t
  disjoint E b
  disjoint E s
  disjoint E t
  disjoint F b
  disjoint F s
  disjoint F t
  disjoint X b
  disjoint X s
  disjoint X t
  disjoint b ph
  disjoint ph s
  disjoint ph t
  disjoint A c
  disjoint b c
  disjoint c s
  disjoint c t
  disjoint B c
  disjoint C c
  disjoint F c
  disjoint X c
  disjoint c ph
  disjoint k x
  assert |- ( ph -> ( dom ( RR _D O ) = ( A (,) B ) /\ E. b e. RR A. s e. dom ( RR _D O ) ( abs ` ( ( RR _D O ) ` s ) ) <_ b ) )

  proof
    wph
    cr
    cO
    cdv
    co
    #
    cdm
    #
    cA
    cB
    cioo
    co
    #
    wceq
    #
    vs
    cv
    #
    @0
    cfv
    #
    cabs
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vs
    @1
    wral
    vb
    cr
    wrex
    #
    wph
    @2
    cr
    @0
    wf
    #
    @3
    wph
    @10
    @0
    vs
    @2
    cX
    @4
    caddc
    co
    #
    cr
    cF
    cX
    cA
    caddc
    co
    #
    cX
    cB
    caddc
    co
    #
    cioo
    co
    #
    cres
    cdv
    co
    #
    cfv
    #
    c2
    @4
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmul
    co
    @17
    ccos
    cfv
    #
    @11
    cF
    cfv
    #
    cC
    cmin
    co
    #
    cmul
    co
    cmin
    co
    @19
    c2
    cexp
    co
    cdiv
    co
    cmpt
    wceq
    #
    wph
    @10
    @23
    wa
    wi
    #
    cr
    vs
    @2
    @19
    cmpt
    cdv
    co
    vs
    @2
    @20
    cmpt
    wceq
    #
    wph
    cA
    cB
    cC
    cF
    cO
    cX
    vs
    fourierdlem68.f
    fourierdlem68.xre
    fourierdlem68.a
    fourierdlem68.b
    fourierdlem68.fdv
    wph
    @2
    cA
    cB
    cicc
    co
    #
    cpi
    cneg
    cpi
    cicc
    co
    #
    cA
    cB
    ioossicc
    #
    fourierdlem68.ab
    syl5ss
    wph
    cc0
    @26
    wcel
    #
    cc0
    @2
    wcel
    fourierdlem68.n0
    @2
    @26
    cc0
    @28
    sseli
    nsyl
    fourierdlem68.c
    fourierdlem68.o
    fourierdlem57
    #
    simpli
    simpld
    @2
    cr
    @0
    fdm
    syl
    #
    wph
    @9
    @4
    cr
    vs
    @2
    @22
    @19
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    vs
    @1
    wral
    #
    vb
    cr
    wrex
    #
    wph
    @39
    @37
    vs
    @2
    wral
    #
    vb
    cr
    wrex
    #
    wph
    vc
    cv
    #
    c2
    vt
    cv
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vt
    @26
    wral
    #
    vc
    crp
    wrex
    @41
    wph
    vt
    vc
    cA
    cB
    @46
    vt
    @26
    @46
    cmpt
    #
    @50
    eqid
    #
    fourierdlem68.a
    fourierdlem68.b
    wph
    cA
    cB
    fourierdlem68.a
    fourierdlem68.b
    fourierdlem68.altb
    ltled
    wph
    @50
    @26
    cr
    cc0
    csn
    #
    cdif
    #
    ccncf
    co
    wcel
    #
    @26
    @53
    @50
    wf
    #
    wph
    vt
    @26
    @46
    @53
    @50
    wph
    @43
    @26
    wcel
    #
    wa
    #
    @46
    cr
    wcel
    @46
    cc0
    wne
    @46
    @53
    wcel
    @57
    c2
    @45
    c2
    cr
    wcel
    #
    @57
    2re
    a1i
    @57
    @44
    @57
    @43
    wph
    @26
    cr
    @43
    wph
    cA
    cB
    fourierdlem68.a
    fourierdlem68.b
    iccssred
    #
    sselda
    rehalfcld
    resincld
    #
    remulcld
    @57
    c2
    @45
    @57
    2cnd
    #
    @57
    @45
    @60
    recnd
    c2
    cc0
    wne
    #
    @57
    2ne0
    a1i
    #
    @57
    @43
    @27
    wcel
    @43
    cc0
    wne
    @45
    cc0
    wne
    wph
    @26
    @27
    @43
    fourierdlem68.ab
    sselda
    @57
    @43
    cc0
    @57
    @43
    cc0
    wceq
    #
    @29
    @56
    @64
    @29
    wph
    @56
    @64
    wa
    cc0
    @43
    @26
    @64
    cc0
    @43
    wceq
    #
    @56
    @64
    @65
    @43
    cc0
    eqcom
    biimpi
    adantl
    @56
    @64
    simpl
    eqeltrd
    adantll
    wph
    @29
    wn
    @56
    @64
    fourierdlem68.n0
    ad2antrr
    pm2.65da
    neqned
    @43
    fourierdlem44
    syl2anc
    mulne0d
    @46
    cr
    cc0
    eldifsn
    sylanbrc
    @51
    fmptd
    wph
    @53
    cc
    wss
    #
    @50
    @26
    cc
    ccncf
    co
    #
    wcel
    @54
    @55
    wb
    @66
    wph
    @53
    cr
    cc
    cr
    @52
    difss
    ax-resscn
    sstri
    a1i
    wph
    vt
    c2
    @45
    @26
    wph
    vt
    @26
    c2
    cc
    wph
    @26
    cr
    cc
    @59
    ax-resscn
    syl6ss
    #
    wph
    2cnd
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    #
    constcncfg
    #
    wph
    vt
    @44
    csin
    @26
    csin
    cc
    cc
    ccncf
    co
    wcel
    wph
    sincn
    a1i
    wph
    vt
    @43
    c2
    @26
    wph
    vt
    @26
    cc
    @68
    @69
    idcncfg
    wph
    vt
    @26
    c2
    cmpt
    #
    @26
    cc
    @52
    cdif
    #
    ccncf
    co
    wcel
    #
    @26
    @72
    @71
    wf
    #
    wph
    vt
    @26
    c2
    @72
    @71
    @57
    c2
    cc
    wcel
    @62
    c2
    @72
    wcel
    @61
    @63
    c2
    cc
    cc0
    eldifsn
    sylanbrc
    @71
    eqid
    fmptd
    wph
    @72
    cc
    wss
    @71
    @67
    wcel
    @73
    @74
    wb
    wph
    cc
    @52
    difssd
    @70
    @26
    cc
    @72
    @71
    cncffvrn
    syl2anc
    mpbird
    divcncf
    cncfmpt1f
    mulcncf
    @26
    cc
    @53
    @50
    cncffvrn
    syl2anc
    mpbird
    cncficcgt0
    wph
    @49
    @41
    vc
    crp
    wph
    @42
    crp
    wcel
    #
    @49
    w3a
    #
    vs
    @22
    @19
    @16
    @20
    cD
    cC
    cabs
    cfv
    #
    caddc
    co
    #
    c2
    c1
    cmul
    co
    #
    cr
    c1
    cE
    @42
    @34
    @2
    vb
    cr
    cr
    cc
    cpr
    wcel
    #
    @76
    reelprrecn
    a1i
    wph
    @75
    @4
    @2
    wcel
    #
    @22
    cc
    wcel
    @49
    wph
    @81
    wa
    #
    @22
    @82
    @21
    cC
    @82
    cr
    cr
    @11
    cF
    wph
    cr
    cr
    cF
    wf
    @81
    fourierdlem68.f
    adantr
    @82
    cX
    @4
    wph
    cX
    cr
    wcel
    @81
    fourierdlem68.xre
    adantr
    #
    @81
    @4
    cr
    wcel
    wph
    @4
    cA
    cB
    elioore
    #
    adantl
    #
    readdcld
    #
    ffvelrnd
    #
    wph
    cC
    cr
    wcel
    @81
    fourierdlem68.c
    adantr
    #
    resubcld
    recnd
    #
    3ad2antl1
    wph
    @75
    cr
    vs
    @2
    @22
    cmpt
    cdv
    co
    #
    vs
    @2
    @16
    cmpt
    #
    wceq
    @49
    wph
    @90
    vs
    @2
    @16
    cc0
    cmin
    co
    #
    cmpt
    @91
    wph
    vs
    @21
    @16
    cC
    cc0
    cr
    cr
    cr
    @2
    @80
    wph
    reelprrecn
    a1i
    #
    @82
    @21
    @87
    recnd
    #
    @82
    @14
    cr
    @11
    @15
    wph
    @14
    cr
    @15
    wf
    @81
    fourierdlem68.fdv
    adantr
    @82
    @12
    @13
    @11
    wph
    @12
    cxr
    wcel
    @81
    wph
    @12
    wph
    cX
    cA
    fourierdlem68.xre
    fourierdlem68.a
    readdcld
    rexrd
    adantr
    wph
    @13
    cxr
    wcel
    @81
    wph
    @13
    wph
    cX
    cB
    fourierdlem68.xre
    fourierdlem68.b
    readdcld
    rexrd
    adantr
    @86
    @82
    cA
    @4
    cX
    wph
    cA
    cr
    wcel
    @81
    fourierdlem68.a
    adantr
    #
    @85
    @83
    @82
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @81
    cA
    @4
    clt
    wbr
    @82
    cA
    @95
    rexrd
    #
    wph
    @97
    @81
    wph
    cB
    fourierdlem68.b
    rexrd
    adantr
    #
    wph
    @81
    simpr
    #
    cA
    cB
    @4
    ioogtlb
    syl3anc
    ltadd2dd
    @82
    @4
    cB
    cX
    @85
    wph
    cB
    cr
    wcel
    @81
    fourierdlem68.b
    adantr
    @83
    @82
    @96
    @97
    @81
    @4
    cB
    clt
    wbr
    @98
    @99
    @100
    cA
    cB
    @4
    iooltub
    syl3anc
    ltadd2dd
    eliood
    #
    ffvelrnd
    #
    wph
    cA
    cB
    @15
    cF
    cX
    vs
    fourierdlem68.f
    fourierdlem68.xre
    fourierdlem68.a
    fourierdlem68.b
    @15
    eqid
    fourierdlem68.fdv
    fourierdlem28
    @82
    cC
    @88
    recnd
    #
    @82
    0red
    wph
    vs
    @2
    cC
    cr
    @93
    @2
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    wph
    @2
    cioo
    crn
    ctg
    cfv
    @105
    cA
    cB
    iooretop
    @104
    @104
    eqid
    tgioo2
    eleqtri
    a1i
    wph
    cC
    fourierdlem68.c
    recnd
    #
    dvmptconst
    dvmptsub
    wph
    vs
    @2
    @92
    @16
    @82
    @16
    @82
    @16
    @102
    recnd
    #
    subid1d
    mpteq2dva
    eqtrd
    3ad2ant1
    wph
    @75
    @81
    @16
    cc
    wcel
    @49
    @107
    3ad2antl1
    @81
    @19
    cc
    wcel
    @76
    @81
    c2
    @18
    @81
    2cnd
    #
    @81
    @17
    @81
    @4
    @81
    @4
    @84
    recnd
    halfcld
    #
    sincld
    #
    mulcld
    adantl
    wph
    @75
    cE
    cr
    wcel
    @49
    fourierdlem68.e
    3ad2ant1
    @79
    cr
    wcel
    @76
    c2
    c1
    2re
    1re
    remulcli
    a1i
    @76
    1red
    wph
    @75
    @78
    cr
    wcel
    @49
    wph
    cD
    @77
    fourierdlem68.d
    wph
    cC
    @106
    abscld
    readdcld
    3ad2ant1
    wph
    @75
    @81
    @16
    cabs
    cfv
    #
    cE
    cle
    wbr
    #
    @49
    @82
    @11
    cr
    wcel
    wph
    @11
    @14
    wcel
    #
    wa
    #
    @112
    @86
    @82
    wph
    @113
    wph
    @81
    simpl
    @101
    jca
    #
    wph
    @43
    @14
    wcel
    #
    wa
    #
    @43
    @15
    cfv
    #
    cabs
    cfv
    #
    cE
    cle
    wbr
    #
    wi
    @114
    @112
    wi
    vt
    @11
    cr
    @43
    @11
    wceq
    #
    @117
    @114
    @120
    @112
    @121
    @116
    @113
    wph
    @43
    @11
    @14
    eleq1
    anbi2d
    #
    @121
    @119
    @111
    cE
    cle
    @121
    @118
    @16
    cabs
    @43
    @11
    @15
    fveq2
    fveq2d
    breq1d
    imbi12d
    fourierdlem68.fdvbd
    vtoclg
    sylc
    3ad2antl1
    @81
    @19
    cabs
    cfv
    #
    @79
    cle
    wbr
    @76
    @81
    @123
    c2
    cabs
    cfv
    #
    @18
    cabs
    cfv
    #
    cmul
    co
    #
    @79
    cle
    @81
    c2
    @18
    @108
    @110
    absmuld
    @81
    @126
    c2
    @125
    cmul
    co
    @79
    cle
    @124
    c2
    @125
    cmul
    @58
    cc0
    c2
    cle
    wbr
    #
    @124
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    oveq1i
    @81
    @125
    c1
    c2
    @81
    @18
    @110
    abscld
    @81
    1red
    @58
    @81
    2re
    a1i
    @127
    @81
    0le2
    a1i
    @81
    @17
    cr
    wcel
    #
    @125
    c1
    cle
    wbr
    @81
    @4
    @84
    rehalfcld
    #
    @17
    abssinbd
    syl
    lemul2ad
    syl5eqbr
    eqbrtrd
    adantl
    wph
    @75
    @81
    @20
    cabs
    cfv
    c1
    cle
    wbr
    #
    @49
    @82
    @81
    @128
    @130
    @100
    @129
    @17
    abscosbd
    3syl
    3ad2antl1
    wph
    @75
    @81
    @22
    cabs
    cfv
    #
    @78
    cle
    wbr
    @49
    @82
    @131
    @21
    cabs
    cfv
    #
    @77
    caddc
    co
    @78
    @82
    @22
    @89
    abscld
    @82
    @132
    @77
    @82
    @21
    @94
    abscld
    #
    @82
    cC
    @103
    abscld
    #
    readdcld
    @82
    cD
    @77
    wph
    cD
    cr
    wcel
    @81
    fourierdlem68.d
    adantr
    #
    @134
    readdcld
    @82
    @21
    cC
    @94
    @103
    abs2dif2d
    @82
    @132
    cD
    @77
    @133
    @135
    @134
    @82
    @113
    @114
    @132
    cD
    cle
    wbr
    #
    @101
    @115
    @117
    @43
    cF
    cfv
    #
    cabs
    cfv
    #
    cD
    cle
    wbr
    #
    wi
    @114
    @136
    wi
    vt
    @11
    @14
    @121
    @117
    @114
    @139
    @136
    @122
    @121
    @138
    @132
    cD
    cle
    @121
    @137
    @21
    cabs
    @43
    @11
    cF
    fveq2
    fveq2d
    breq1d
    imbi12d
    fourierdlem68.fbd
    vtoclg
    sylc
    leadd1dd
    letrd
    3ad2antl1
    @25
    @76
    @24
    @25
    @30
    simpri
    a1i
    @81
    @20
    cc
    wcel
    @76
    @81
    @17
    @109
    coscld
    adantl
    wph
    @75
    @49
    simp2
    wph
    @49
    @42
    @123
    cle
    wbr
    #
    vs
    @2
    wral
    #
    @75
    @49
    wph
    @140
    vs
    @26
    wral
    #
    @141
    @48
    @140
    vt
    vs
    @26
    @43
    @4
    wceq
    #
    @47
    @123
    @42
    cle
    @143
    @46
    @19
    cabs
    @143
    @45
    @18
    c2
    cmul
    @143
    @44
    @17
    csin
    @43
    @4
    c2
    cdiv
    oveq1
    fveq2d
    oveq2d
    fveq2d
    breq2d
    cbvralv
    wph
    @142
    wa
    #
    @140
    vs
    @2
    wph
    @142
    vs
    wph
    vs
    nfv
    @140
    vs
    @26
    nfra1
    nfan
    @144
    @81
    @140
    @144
    @81
    wa
    @142
    @4
    @26
    wcel
    #
    @140
    wph
    @142
    @81
    simplr
    wph
    @81
    @145
    @142
    @82
    @2
    @26
    @4
    @28
    @100
    sseldi
    adantlr
    @140
    vs
    @26
    rspa
    syl2anc
    ex
    ralrimi
    sylan2b
    3adant2
    @34
    eqid
    dvdivbd
    rexlimdv3a
    mpd
    wph
    @38
    @40
    vb
    cr
    wph
    @3
    @38
    @40
    wb
    @31
    @37
    vs
    @1
    @2
    vs
    @0
    vs
    cr
    cO
    cdv
    vs
    cr
    nfcv
    vs
    cdv
    nfcv
    vs
    cO
    @33
    fourierdlem68.o
    vs
    @2
    @32
    nfmpt1
    nfcxfr
    nfov
    nfdm
    vs
    @2
    nfcv
    raleqf
    syl
    rexbidv
    mpbird
    wph
    @8
    @37
    vb
    vs
    cr
    @1
    wph
    @6
    @36
    @7
    cle
    wph
    @5
    @35
    cabs
    wph
    @4
    @0
    @34
    wph
    cO
    @33
    cr
    cdv
    cO
    @33
    wceq
    wph
    fourierdlem68.o
    a1i
    oveq2d
    fveq1d
    fveq2d
    breq1d
    rexralbidv
    mpbird
    jca
end
