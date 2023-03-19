include "cv.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "cvol.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "citg.mm"
include "cabs.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "cn.mm"
include "wral.mm"
include "wi.mm"
include "cdm.mm"
include "wrex.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "csin.mm"
include "fourierdlem77.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "jca31.mm"
include "simpr.mm"
include "simpllr.mm"
include "rspa.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cr.mm"
include "fourierdlem55.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "wf.mm"
include "nnre.mm"
include "fourierdlem5.mm"
include "syl.mm"
include "ad2antlr.mm"
include "ffvelrnd.mm"
include "remulcld.mm"
include "fvmpt2.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "adantr.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "resincld.mm"
include "oveq2d.mm"
include "adantll.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "recnd.mm"
include "absmuld.mm"
include "adantllr.mm"
include "abscld.mm"
include "rpre.mm"
include "ad4antlr.mm"
include "1red.mm"
include "absge0d.mm"
include "abssinbd.mm"
include "lemul2ad.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralrimiva.mm"
include "reximdva.mm"
include "mpd.mm"
include "w3a.mm"
include "c3.mm"
include "id.mm"
include "3rp.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
include "3adant3.mm"
include "nf3an.mm"
include "simpl1l.mm"
include "ad2antrr.mm"
include "sylbi.mm"
include "fourierdlem67.mm"
include "simplrl.mm"
include "sselda.mm"
include "cmpt.mm"
include "cibl.mm"
include "feqmptd.mm"
include "simprbi.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "itgcl.mm"
include "iblabs.mm"
include "itgrecl.mm"
include "simpl1r.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "itgabs.mm"
include "simpl2.mm"
include "cc.mm"
include "cxr.mm"
include "cmnf.mm"
include "cc0.mm"
include "cpnf.mm"
include "iccssxr.mm"
include "volf.mm"
include "sseldi.mm"
include "iccvolcl.mm"
include "mnfxr.mm"
include "0xr.mm"
include "mnflt0.mm"
include "volge0.mm"
include "xrltletrd.mm"
include "iccmbl.mm"
include "volss.mm"
include "syl3anc.mm"
include "xrre.mm"
include "syl22anc.mm"
include "rpcnd.mm"
include "iblconstmpt.mm"
include "simpl3.mm"
include "itgle.mm"
include "itgconst.mm"
include "3re.mm"
include "wne.mm"
include "3ne0.mm"
include "redivcld.mm"
include "rpne0d.mm"
include "rpge0d.mm"
include "simplrr.mm"
include "oveq2i.mm"
include "divcan2d.mm"
include "syl5eq.mm"
include "2rp.mm"
include "2lt3.mm"
include "ltdiv2dd.mm"
include "lelttrd.mm"
include "sylbir.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdv3a.mm"
include "wb.mm"
include "simplll.mm"
include "sseldd.mm"
include "itgeq2dv.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "adantrr.mm"
include "pm5.74da.mm"
include "rexralbidv.mm"
include "mpbid.mm"

theorem fourierdlem87
  let wph: wff ph
  let wch: wff ch
  let vx: setvar x
  let vu: setvar u
  let cD: class D
  let cS: class S
  let cU: class U
  let ve: setvar e
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let va: setvar a
  let vd: setvar d
  assume fourierdlem87.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem87.x: |- ( ph -> X e. RR )
  assume fourierdlem87.y: |- ( ph -> Y e. RR )
  assume fourierdlem87.w: |- ( ph -> W e. RR )
  assume fourierdlem87.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem87.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem87.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem87.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem87.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )
  assume fourierdlem87.10: |- ( ph -> E. x e. RR A. s e. ( -u _pi [,] _pi ) ( abs ` ( H ` s ) ) <_ x )
  assume fourierdlem87.gibl: |- ( ( ph /\ n e. NN ) -> G e. L^1 )
  assume fourierdlem87.d: |- D = ( ( e / 3 ) / a )
  assume fourierdlem87.ch: |- ( ch <-> ( ( ( ( ( ph /\ e e. RR+ ) /\ a e. RR+ /\ A. n e. NN A. s e. ( -u _pi [,] _pi ) ( abs ` ( G ` s ) ) <_ a ) /\ u e. dom vol ) /\ ( u C_ ( -u _pi [,] _pi ) /\ ( vol ` u ) <_ D ) ) /\ n e. NN ) )

  disjoint D d
  disjoint D n
  disjoint D u
  disjoint d n
  disjoint d u
  disjoint n u
  disjoint G a
  disjoint G d
  disjoint G s
  disjoint G u
  disjoint a d
  disjoint a s
  disjoint a u
  disjoint d s
  disjoint s u
  disjoint K a
  disjoint K s
  disjoint U a
  disjoint U n
  disjoint a n
  disjoint U k
  disjoint k n
  disjoint U x
  disjoint a x
  disjoint a e
  disjoint d e
  disjoint e n
  disjoint e u
  disjoint a ph
  disjoint d ph
  disjoint n ph
  disjoint n s
  disjoint ph s
  disjoint ph u
  disjoint ch s
  disjoint e k
  disjoint k u
  disjoint k s
  disjoint ph x
  disjoint s x
  disjoint k x
  assert |- ( ( ph /\ e e. RR+ ) -> E. d e. RR+ A. u e. dom vol ( ( u C_ ( -u _pi [,] _pi ) /\ ( vol ` u ) <_ d ) -> A. k e. NN ( abs ` S. u ( ( U ` s ) x. ( sin ` ( ( k + ( 1 / 2 ) ) x. s ) ) ) _d s ) < ( e / 2 ) ) )

  proof
    wph
    ve
    cv
    #
    crp
    wcel
    #
    wa
    #
    vu
    cv
    #
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wss
    #
    @3
    cvol
    cfv
    #
    vd
    cv
    #
    cle
    wbr
    #
    wa
    #
    vs
    @3
    vs
    cv
    #
    cG
    cfv
    #
    citg
    #
    cabs
    cfv
    #
    @0
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vn
    cn
    wral
    #
    wi
    #
    vu
    cvol
    cdm
    #
    wral
    #
    vd
    crp
    wrex
    #
    @10
    vs
    @3
    @11
    cU
    cfv
    #
    vk
    cv
    #
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @11
    cmul
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    citg
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    vk
    cn
    wral
    #
    wi
    #
    vu
    @19
    wral
    vd
    crp
    wrex
    #
    @2
    @12
    cabs
    cfv
    #
    va
    cv
    #
    cle
    wbr
    #
    vs
    @5
    wral
    #
    vn
    cn
    wral
    #
    va
    crp
    wrex
    #
    @21
    wph
    @40
    @1
    wph
    @22
    cabs
    cfv
    #
    @36
    cle
    wbr
    #
    vs
    @5
    wral
    #
    va
    crp
    wrex
    @40
    wph
    cU
    cF
    cH
    cK
    cW
    cX
    cY
    vs
    vx
    va
    fourierdlem87.f
    fourierdlem87.x
    fourierdlem87.y
    fourierdlem87.w
    fourierdlem87.h
    fourierdlem87.k
    fourierdlem87.u
    fourierdlem87.10
    fourierdlem77
    wph
    @43
    @39
    va
    crp
    wph
    @36
    crp
    wcel
    #
    wa
    #
    @43
    @39
    @45
    @43
    wa
    #
    @38
    vn
    cn
    @46
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    @37
    vs
    @5
    @46
    @48
    vs
    @45
    @43
    vs
    @45
    vs
    nfv
    @42
    vs
    @5
    nfra1
    nfan
    @48
    vs
    nfv
    nfan
    @49
    @11
    @5
    wcel
    #
    @37
    @49
    @50
    wa
    #
    @45
    @48
    wa
    #
    @50
    @42
    @37
    @51
    wph
    @44
    @48
    wph
    @44
    @43
    @48
    @50
    simp-4l
    wph
    @44
    @43
    @48
    @50
    simp-4r
    @46
    @48
    @50
    simplr
    jca31
    @49
    @50
    simpr
    #
    @51
    @43
    @50
    @42
    @45
    @43
    @48
    @50
    simpllr
    @53
    @42
    vs
    @5
    rspa
    syl2anc
    @52
    @50
    wa
    #
    @42
    wa
    #
    @35
    @41
    @47
    @24
    caddc
    co
    #
    @11
    cmul
    co
    #
    csin
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @36
    cle
    @54
    @35
    @60
    wceq
    #
    @42
    wph
    @48
    @50
    @61
    @44
    wph
    @48
    wa
    #
    @50
    wa
    #
    @35
    @22
    @58
    cmul
    co
    #
    cabs
    cfv
    @60
    @63
    @12
    @64
    cabs
    @63
    @12
    @22
    @11
    cS
    cfv
    #
    cmul
    co
    #
    @64
    @63
    @50
    @66
    cr
    wcel
    @12
    @66
    wceq
    @62
    @50
    simpr
    #
    @63
    @22
    @65
    wph
    @50
    @22
    cr
    wcel
    @48
    wph
    @5
    cr
    @11
    cU
    wph
    cU
    cF
    cH
    cK
    cW
    cX
    cY
    vs
    fourierdlem87.f
    fourierdlem87.x
    fourierdlem87.y
    fourierdlem87.w
    fourierdlem87.h
    fourierdlem87.k
    fourierdlem87.u
    fourierdlem55
    ffvelrnda
    adantlr
    #
    @63
    @5
    cr
    @11
    cS
    @48
    @5
    cr
    cS
    wf
    #
    wph
    @50
    @48
    @47
    cr
    wcel
    #
    @69
    @47
    nnre
    #
    vs
    cS
    @47
    fourierdlem87.s
    fourierdlem5
    syl
    ad2antlr
    @67
    ffvelrnd
    remulcld
    vs
    @5
    @66
    cr
    cG
    fourierdlem87.g
    fvmpt2
    syl2anc
    @48
    @50
    @66
    @64
    wceq
    wph
    @48
    @50
    wa
    #
    @65
    @58
    @22
    cmul
    @72
    @50
    @58
    cr
    wcel
    #
    @65
    @58
    wceq
    @48
    @50
    simpr
    @72
    @57
    @72
    @56
    @11
    @48
    @56
    cr
    wcel
    @50
    @48
    @47
    @24
    @71
    @24
    cr
    wcel
    @48
    halfre
    a1i
    readdcld
    adantr
    @50
    @11
    cr
    wcel
    @48
    @5
    cr
    @11
    @4
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @5
    cr
    wss
    cpi
    pire
    renegcli
    #
    pire
    @4
    cpi
    iccssre
    mp2an
    sseli
    adantl
    remulcld
    #
    resincld
    #
    vs
    @5
    @58
    cr
    cS
    fourierdlem87.s
    fvmpt2
    syl2anc
    oveq2d
    adantll
    eqtrd
    #
    fveq2d
    @63
    @22
    @58
    @63
    @22
    @68
    recnd
    #
    @63
    @58
    @48
    @50
    @73
    wph
    @78
    adantll
    recnd
    #
    absmuld
    eqtrd
    adantllr
    adantr
    @55
    @60
    @41
    @36
    @54
    @60
    cr
    wcel
    #
    @42
    wph
    @48
    @50
    @82
    @44
    @63
    @41
    @59
    @63
    @22
    @80
    abscld
    #
    @63
    @58
    @81
    abscld
    #
    remulcld
    adantllr
    adantr
    @54
    @41
    cr
    wcel
    #
    @42
    wph
    @48
    @50
    @85
    @44
    @83
    adantllr
    adantr
    @44
    @36
    cr
    wcel
    #
    wph
    @48
    @50
    @42
    @36
    rpre
    ad4antlr
    @54
    @60
    @41
    cle
    wbr
    #
    @42
    wph
    @48
    @50
    @87
    @44
    @63
    @60
    @41
    c1
    cmul
    co
    @41
    cle
    @63
    @59
    c1
    @41
    @84
    @63
    1red
    @83
    @63
    @22
    @80
    absge0d
    @63
    @57
    cr
    wcel
    #
    @59
    c1
    cle
    wbr
    @48
    @50
    @88
    wph
    @77
    adantll
    @57
    abssinbd
    syl
    lemul2ad
    @63
    @41
    @63
    @41
    @83
    recnd
    mulid1d
    breqtrd
    adantllr
    adantr
    @54
    @42
    simpr
    letrd
    eqbrtrd
    syl21anc
    ex
    ralrimi
    ralrimiva
    ex
    reximdva
    mpd
    adantr
    @2
    @39
    @21
    va
    crp
    @2
    @44
    @39
    w3a
    #
    cD
    crp
    wcel
    #
    @6
    @7
    cD
    cle
    wbr
    #
    wa
    #
    @17
    wi
    #
    vu
    @19
    wral
    #
    @21
    @2
    @44
    @90
    @39
    @1
    @44
    @90
    wph
    @1
    @44
    wa
    #
    cD
    @0
    c3
    cdiv
    co
    #
    @36
    cdiv
    co
    #
    crp
    fourierdlem87.d
    @95
    @96
    @36
    @1
    @96
    crp
    wcel
    @44
    @1
    @0
    c3
    @1
    id
    c3
    crp
    wcel
    #
    @1
    3rp
    a1i
    rpdivcld
    adantr
    @1
    @44
    simpr
    rpdivcld
    syl5eqel
    adantll
    3adant3
    @89
    @93
    vu
    @19
    @89
    @3
    @19
    wcel
    #
    wa
    #
    @92
    @17
    @100
    @92
    wa
    #
    @16
    vn
    cn
    @100
    @92
    vn
    @89
    @99
    vn
    @2
    @44
    @39
    vn
    @2
    vn
    nfv
    @44
    vn
    nfv
    @38
    vn
    cn
    nfra1
    nf3an
    @99
    vn
    nfv
    nfan
    @92
    vn
    nfv
    nfan
    @101
    @48
    @16
    @101
    @48
    wa
    #
    wch
    @16
    fourierdlem87.ch
    wch
    @14
    vs
    @3
    @35
    citg
    #
    @15
    wch
    @13
    wch
    vs
    @3
    @12
    cr
    wch
    @11
    @3
    wcel
    #
    wa
    #
    @5
    cr
    @11
    cG
    wch
    @5
    cr
    cG
    wf
    @104
    wch
    cS
    cU
    cF
    cG
    cH
    cK
    @47
    cW
    cX
    cY
    vs
    wch
    wph
    cr
    cr
    cF
    wf
    wch
    @102
    wph
    fourierdlem87.ch
    @100
    wph
    @92
    @48
    wph
    @1
    @44
    @39
    @99
    simpl1l
    ad2antrr
    sylbi
    #
    fourierdlem87.f
    syl
    wch
    wph
    cX
    cr
    wcel
    @106
    fourierdlem87.x
    syl
    wch
    wph
    cY
    cr
    wcel
    @106
    fourierdlem87.y
    syl
    wch
    wph
    cW
    cr
    wcel
    @106
    fourierdlem87.w
    syl
    fourierdlem87.h
    fourierdlem87.k
    fourierdlem87.u
    wch
    @102
    @70
    fourierdlem87.ch
    @48
    @70
    @101
    @71
    adantl
    sylbi
    fourierdlem87.s
    fourierdlem87.g
    fourierdlem67
    #
    adantr
    wch
    @3
    @5
    @11
    wch
    @102
    @6
    fourierdlem87.ch
    @100
    @6
    @91
    @48
    simplrl
    sylbi
    #
    sselda
    #
    ffvelrnd
    #
    wch
    vs
    @3
    @5
    @12
    cr
    @108
    wch
    @102
    @99
    fourierdlem87.ch
    @89
    @99
    @92
    @48
    simpllr
    sylbi
    #
    wch
    @5
    cr
    @11
    cG
    @107
    ffvelrnda
    wch
    cG
    vs
    @5
    @12
    cmpt
    cibl
    wch
    vs
    @5
    cr
    cG
    @107
    feqmptd
    wch
    wph
    @48
    cG
    cibl
    wcel
    @106
    wch
    @101
    @48
    fourierdlem87.ch
    simprbi
    #
    fourierdlem87.gibl
    syl2anc
    eqeltrrd
    iblss
    #
    itgcl
    abscld
    wch
    vs
    @3
    @35
    @105
    @12
    @105
    @12
    @110
    recnd
    abscld
    #
    wch
    vs
    @3
    @12
    cr
    @110
    @113
    iblabs
    #
    itgrecl
    #
    wch
    @0
    wch
    @0
    wch
    @102
    @1
    fourierdlem87.ch
    @100
    @1
    @92
    @48
    wph
    @1
    @44
    @39
    @99
    simpl1r
    ad2antrr
    sylbi
    #
    rpred
    #
    rehalfcld
    #
    wch
    vs
    @3
    @12
    cr
    @110
    @113
    itgabs
    wch
    @103
    vs
    @3
    @36
    citg
    #
    @15
    @116
    wch
    vs
    @3
    @36
    wch
    @86
    @104
    wch
    @36
    wch
    @102
    @44
    fourierdlem87.ch
    @100
    @44
    @92
    @48
    @2
    @44
    @39
    @99
    simpl2
    ad2antrr
    sylbi
    #
    rpred
    #
    adantr
    #
    wch
    @99
    @7
    cr
    wcel
    #
    @36
    cc
    wcel
    #
    vs
    @3
    @36
    cmpt
    cibl
    wcel
    @111
    wch
    @7
    cxr
    wcel
    @5
    cvol
    cfv
    #
    cr
    wcel
    #
    cmnf
    @7
    clt
    wbr
    @7
    @126
    cle
    wbr
    #
    @124
    wch
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @7
    cc0
    cpnf
    iccssxr
    wch
    @19
    @129
    @3
    cvol
    @19
    @129
    cvol
    wf
    wch
    volf
    a1i
    @111
    ffvelrnd
    sseldi
    #
    @127
    wch
    @74
    @75
    @127
    @76
    pire
    @4
    cpi
    iccvolcl
    mp2an
    a1i
    wch
    cmnf
    cc0
    @7
    cmnf
    cxr
    wcel
    wch
    mnfxr
    a1i
    cc0
    cxr
    wcel
    wch
    0xr
    a1i
    @130
    cmnf
    cc0
    clt
    wbr
    wch
    mnflt0
    a1i
    wch
    @99
    cc0
    @7
    cle
    wbr
    @111
    @3
    volge0
    syl
    xrltletrd
    wch
    @99
    @5
    @19
    wcel
    #
    @6
    @128
    @111
    @131
    wch
    @74
    @75
    @131
    @76
    pire
    @4
    cpi
    iccmbl
    mp2an
    a1i
    @108
    @3
    @5
    volss
    syl3anc
    @7
    @126
    xrre
    syl22anc
    #
    wch
    @36
    @121
    rpcnd
    #
    vs
    @3
    @36
    iblconstmpt
    syl3anc
    #
    itgrecl
    @119
    wch
    vs
    @3
    @35
    @36
    @115
    @134
    @114
    @123
    @105
    @38
    @50
    @37
    wch
    @38
    @104
    wch
    @39
    @48
    @38
    wch
    @102
    @39
    fourierdlem87.ch
    @100
    @39
    @92
    @48
    @2
    @44
    @39
    @99
    simpl3
    ad2antrr
    sylbi
    @112
    @38
    vn
    cn
    rspa
    syl2anc
    adantr
    @109
    @37
    vs
    @5
    rspa
    syl2anc
    itgle
    wch
    @120
    @36
    @7
    cmul
    co
    #
    @15
    clt
    wch
    @99
    @124
    @125
    @120
    @135
    wceq
    @111
    @132
    @133
    vs
    @3
    @36
    itgconst
    syl3anc
    wch
    @135
    @36
    cD
    cmul
    co
    #
    @15
    wch
    @36
    @7
    @122
    @132
    remulcld
    wch
    @36
    cD
    @122
    wch
    cD
    @97
    cr
    fourierdlem87.d
    wch
    @96
    @36
    wch
    @0
    c3
    @118
    c3
    cr
    wcel
    wch
    3re
    a1i
    c3
    cc0
    wne
    wch
    3ne0
    a1i
    redivcld
    #
    @122
    wch
    @36
    @121
    rpne0d
    #
    redivcld
    syl5eqel
    #
    remulcld
    @119
    wch
    @7
    cD
    @36
    @132
    @139
    @122
    wch
    @36
    @121
    rpge0d
    wch
    @102
    @91
    fourierdlem87.ch
    @100
    @6
    @91
    @48
    simplrr
    sylbi
    lemul2ad
    wch
    @136
    @96
    @15
    clt
    wch
    @136
    @36
    @97
    cmul
    co
    @96
    cD
    @97
    @36
    cmul
    fourierdlem87.d
    oveq2i
    wch
    @96
    @36
    wch
    @96
    @137
    recnd
    @133
    @138
    divcan2d
    syl5eq
    wch
    c2
    c3
    @0
    c2
    crp
    wcel
    wch
    2rp
    a1i
    @98
    wch
    3rp
    a1i
    @117
    c2
    c3
    clt
    wbr
    wch
    2lt3
    a1i
    ltdiv2dd
    eqbrtrd
    lelttrd
    eqbrtrd
    lelttrd
    lelttrd
    sylbir
    ex
    ralrimi
    ex
    ralrimiva
    @20
    @94
    vd
    cD
    crp
    @8
    cD
    wceq
    #
    @18
    @93
    vu
    @19
    @140
    @10
    @92
    @17
    @140
    @9
    @91
    @6
    @8
    cD
    @7
    cle
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rexlimdv3a
    mpd
    wph
    @21
    @34
    wb
    @1
    wph
    @18
    @33
    vd
    vu
    crp
    @19
    wph
    @10
    @17
    @32
    wph
    @6
    @17
    @32
    wb
    @9
    wph
    @6
    wa
    #
    @17
    vs
    @3
    @64
    citg
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    vn
    cn
    wral
    @32
    @141
    @16
    @144
    vn
    cn
    @141
    @48
    wa
    #
    @14
    @143
    @15
    clt
    @145
    @13
    @142
    cabs
    @145
    vs
    @3
    @12
    @64
    @145
    @104
    wa
    #
    wph
    @48
    @50
    @12
    @64
    wceq
    wph
    @6
    @48
    @104
    simplll
    @141
    @48
    @104
    simplr
    @146
    @3
    @5
    @11
    wph
    @6
    @48
    @104
    simpllr
    @145
    @104
    simpr
    sseldd
    @79
    syl21anc
    itgeq2dv
    fveq2d
    breq1d
    ralbidva
    @144
    @31
    vn
    vk
    cn
    @47
    @23
    wceq
    #
    @143
    @30
    @15
    clt
    @147
    @142
    @29
    cabs
    @147
    vs
    @3
    @64
    @28
    @147
    @64
    @28
    wceq
    @104
    @147
    @58
    @27
    @22
    cmul
    @147
    @57
    @26
    csin
    @147
    @56
    @25
    @11
    cmul
    @47
    @23
    @24
    caddc
    oveq1
    oveq1d
    fveq2d
    oveq2d
    adantr
    itgeq2dv
    fveq2d
    breq1d
    cbvralv
    syl6bb
    adantrr
    pm5.74da
    rexralbidv
    adantr
    mpbid
end
