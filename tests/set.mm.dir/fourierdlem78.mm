include "cioo.mm"
include "co.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cr.mm"
include "ccncf.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "wceq.mm"
include "a1i.mm"
include "reseq1d.mm"
include "wcel.mm"
include "wa.mm"
include "pire.mm"
include "renegcli.mm"
include "elioore.mm"
include "adantl.mm"
include "iccssred.mm"
include "sseldd.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "syl.mm"
include "cxr.mm"
include "clt.mm"
include "rexrd.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "lelttrd.mm"
include "ltled.mm"
include "iooltub.mm"
include "simp3bi.mm"
include "ltletrd.mm"
include "eliccd.mm"
include "ex.mm"
include "ssrdv.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "wf.mm"
include "cc0.mm"
include "caddc.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "0red.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "ifcld.mm"
include "resubcld.mm"
include "eleq1.mm"
include "biimpac.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "redivcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "c1.mm"
include "c2.mm"
include "csin.mm"
include "1red.mm"
include "2re.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "remulcld.mm"
include "recnd.mm"
include "wne.mm"
include "2ne0.mm"
include "fourierdlem44.mm"
include "mulne0d.mm"
include "rereccld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "ax-resscn.mm"
include "mpteq2dva.mm"
include "iffalsed.mm"
include "divrecd.mm"
include "3eqtrd.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "addcomd.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "breqtrd.mm"
include "eliood.mm"
include "fvres.mm"
include "ioosscn.mm"
include "fourierdlem23.mm"
include "simplr.mm"
include "adantlr.mm"
include "iftrued.mm"
include "negeqd.mm"
include "renegcld.mm"
include "ssid.mm"
include "constcncfg.mm"
include "simpl.mm"
include "ltnled.mm"
include "mpbird.mm"
include "condan.mm"
include "ltnsymd.mm"
include "negcld.mm"
include "pm2.61dan.mm"
include "addcncf.mm"
include "csn.mm"
include "cdif.mm"
include "1cnd.mm"
include "cdivcncf.mm"
include "wral.mm"
include "velsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "cncfmptssg.mm"
include "mulcncf.mm"
include "eqtr2d.mm"
include "cncfss.mm"
include "mp2an.mm"
include "fourierdlem62.mm"
include "sseldi.mm"
include "sincn.mm"
include "halfre.mm"
include "idcncfg.mm"
include "cncfmpt1f.mm"
include "cncffvrn.mm"

theorem fourierdlem78
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem78.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem78.a: |- ( ph -> A e. ( -u _pi [,] _pi ) )
  assume fourierdlem78.b: |- ( ph -> B e. ( -u _pi [,] _pi ) )
  assume fourierdlem78.x: |- ( ph -> X e. RR )
  assume fourierdlem78.nxelab: |- ( ph -> -. 0 e. ( A (,) B ) )
  assume fourierdlem78.fcn: |- ( ph -> ( F |` ( ( A + X ) (,) ( B + X ) ) ) e. ( ( ( A + X ) (,) ( B + X ) ) -cn-> CC ) )
  assume fourierdlem78.y: |- ( ph -> Y e. RR )
  assume fourierdlem78.w: |- ( ph -> W e. RR )
  assume fourierdlem78.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem78.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem78.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem78.n: |- ( ph -> N e. RR )
  assume fourierdlem78.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( N + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem78.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )

  disjoint A s
  disjoint B s
  disjoint F s
  disjoint N s
  disjoint W s
  disjoint X s
  disjoint Y s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( G |` ( A (,) B ) ) e. ( ( A (,) B ) -cn-> RR ) )

  proof
    wph
    cG
    cA
    cB
    cioo
    co
    #
    cres
    #
    vs
    @0
    vs
    cv
    #
    cU
    cfv
    #
    @2
    cS
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @0
    cr
    ccncf
    co
    #
    wph
    @1
    vs
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    @5
    cmpt
    #
    @0
    cres
    @6
    wph
    cG
    @10
    @0
    cG
    @10
    wceq
    wph
    fourierdlem78.g
    a1i
    reseq1d
    wph
    vs
    @9
    @0
    @5
    wph
    vs
    @0
    @9
    wph
    @2
    @0
    wcel
    #
    @2
    @9
    wcel
    #
    wph
    @11
    wa
    #
    @8
    cpi
    @2
    @8
    cr
    wcel
    #
    @13
    cpi
    pire
    renegcli
    #
    a1i
    #
    cpi
    cr
    wcel
    #
    @13
    pire
    a1i
    #
    @11
    @2
    cr
    wcel
    #
    wph
    @2
    cA
    cB
    elioore
    #
    adantl
    #
    @13
    @8
    @2
    @16
    @21
    @13
    @8
    cA
    @2
    @16
    wph
    cA
    cr
    wcel
    #
    @11
    wph
    @9
    cr
    cA
    wph
    @8
    cpi
    @14
    wph
    @15
    a1i
    @17
    wph
    pire
    a1i
    iccssred
    #
    fourierdlem78.a
    sseldd
    #
    adantr
    #
    @21
    wph
    @8
    cA
    cle
    wbr
    #
    @11
    wph
    cA
    @9
    wcel
    #
    @26
    fourierdlem78.a
    @27
    @22
    @26
    cA
    cpi
    cle
    wbr
    @8
    cpi
    cA
    @15
    pire
    elicc2i
    simp2bi
    syl
    adantr
    @13
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @11
    cA
    @2
    clt
    wbr
    #
    @13
    cA
    @25
    rexrd
    #
    wph
    @29
    @11
    wph
    cB
    wph
    @9
    cr
    cB
    @23
    fourierdlem78.b
    sseldd
    #
    rexrd
    #
    adantr
    #
    wph
    @11
    simpr
    #
    cA
    cB
    @2
    ioogtlb
    syl3anc
    #
    lelttrd
    ltled
    @13
    @2
    cpi
    @21
    @18
    @13
    @2
    cB
    cpi
    @21
    wph
    cB
    cr
    wcel
    #
    @11
    @32
    adantr
    #
    @18
    @13
    @28
    @29
    @11
    @2
    cB
    clt
    wbr
    #
    @31
    @34
    @35
    cA
    cB
    @2
    iooltub
    syl3anc
    #
    wph
    cB
    cpi
    cle
    wbr
    #
    @11
    wph
    cB
    @9
    wcel
    #
    @41
    fourierdlem78.b
    @42
    @37
    @8
    cB
    cle
    wbr
    @41
    @8
    cpi
    cB
    @15
    pire
    elicc2i
    simp3bi
    syl
    adantr
    ltletrd
    ltled
    eliccd
    #
    ex
    ssrdv
    #
    resmptd
    eqtrd
    wph
    @6
    @7
    wcel
    #
    @0
    cr
    @6
    wf
    #
    wph
    vs
    @0
    @5
    cr
    @6
    @13
    @3
    @4
    @13
    @3
    @2
    cH
    cfv
    #
    @2
    cK
    cfv
    #
    cmul
    co
    #
    cr
    @13
    @12
    @49
    cr
    wcel
    @3
    @49
    wceq
    @43
    @13
    @47
    @48
    @13
    @47
    @2
    cc0
    wceq
    #
    cc0
    cX
    @2
    caddc
    co
    #
    cF
    cfv
    #
    cc0
    @2
    clt
    wbr
    #
    cY
    cW
    cif
    #
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cif
    #
    cr
    @13
    @12
    @57
    cr
    wcel
    @47
    @57
    wceq
    @43
    @13
    @50
    cc0
    @56
    cr
    @13
    0red
    @13
    @55
    @2
    @13
    @52
    @54
    @13
    cr
    cr
    @51
    cF
    wph
    cr
    cr
    cF
    wf
    @11
    fourierdlem78.f
    adantr
    @13
    cX
    @2
    wph
    cX
    cr
    wcel
    @11
    fourierdlem78.x
    adantr
    #
    @21
    readdcld
    #
    ffvelrnd
    #
    wph
    @54
    cr
    wcel
    @11
    wph
    @53
    cY
    cW
    cr
    fourierdlem78.y
    fourierdlem78.w
    ifcld
    adantr
    #
    resubcld
    #
    @21
    @13
    @2
    cc0
    @13
    @50
    cc0
    @0
    wcel
    #
    @11
    @50
    @63
    wph
    @50
    @11
    @63
    @2
    cc0
    @0
    eleq1
    biimpac
    adantll
    wph
    @63
    wn
    #
    @11
    @50
    fourierdlem78.nxelab
    ad2antrr
    pm2.65da
    #
    neqned
    #
    redivcld
    ifcld
    #
    vs
    @9
    @57
    cr
    cH
    fourierdlem78.h
    fvmpt2
    syl2anc
    #
    @67
    eqeltrd
    @13
    @48
    @50
    c1
    @2
    c2
    @2
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
    cdiv
    co
    #
    cif
    #
    cr
    @13
    @12
    @73
    cr
    wcel
    @48
    @73
    wceq
    @43
    @13
    @50
    c1
    @72
    cr
    @13
    1red
    @13
    @2
    @71
    @21
    @13
    c2
    @70
    c2
    cr
    wcel
    @13
    2re
    a1i
    #
    @13
    @69
    @13
    @2
    @21
    rehalfcld
    resincld
    #
    remulcld
    #
    @13
    c2
    @70
    @13
    c2
    @74
    recnd
    @13
    @70
    @75
    recnd
    c2
    cc0
    wne
    @13
    2ne0
    a1i
    #
    @13
    @12
    @2
    cc0
    wne
    @70
    cc0
    wne
    @43
    @66
    @2
    fourierdlem44
    syl2anc
    mulne0d
    #
    redivcld
    ifcld
    #
    vs
    @9
    @73
    cr
    cK
    fourierdlem78.k
    fvmpt2
    syl2anc
    #
    @79
    eqeltrd
    remulcld
    #
    vs
    @9
    @49
    cr
    cU
    fourierdlem78.u
    fvmpt2
    syl2anc
    #
    @81
    eqeltrd
    @13
    @4
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @2
    cmul
    co
    #
    csin
    cfv
    #
    cr
    @13
    @12
    @86
    cr
    wcel
    @4
    @86
    wceq
    @43
    @13
    @85
    @13
    @84
    @2
    @13
    cN
    @83
    wph
    cN
    cr
    wcel
    @11
    fourierdlem78.n
    adantr
    @13
    c2
    @74
    @77
    rereccld
    readdcld
    @21
    remulcld
    resincld
    #
    vs
    @9
    @86
    cr
    cS
    fourierdlem78.s
    fvmpt2
    syl2anc
    #
    @87
    eqeltrd
    remulcld
    @6
    eqid
    fmptd
    wph
    cr
    cc
    wss
    #
    @6
    @0
    cc
    ccncf
    co
    #
    wcel
    @45
    @46
    wb
    @89
    wph
    ax-resscn
    a1i
    wph
    vs
    @3
    @4
    @0
    wph
    vs
    @0
    @3
    cmpt
    vs
    @0
    @49
    cmpt
    @90
    wph
    vs
    @0
    @3
    @49
    @82
    mpteq2dva
    wph
    vs
    @47
    @48
    @0
    wph
    vs
    @0
    @47
    cmpt
    vs
    @0
    @55
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    @90
    wph
    vs
    @0
    @47
    @92
    @13
    @47
    @57
    @56
    @92
    @68
    @13
    @50
    cc0
    @56
    @65
    iffalsed
    @13
    @55
    @2
    @13
    @55
    @62
    recnd
    @13
    @2
    @21
    recnd
    #
    @66
    divrecd
    3eqtrd
    mpteq2dva
    wph
    vs
    @55
    @91
    @0
    wph
    vs
    @0
    @55
    cmpt
    vs
    @0
    @52
    @54
    cneg
    #
    caddc
    co
    #
    cmpt
    @90
    wph
    vs
    @0
    @55
    @95
    @13
    @95
    @55
    @13
    @52
    @54
    @13
    @52
    @60
    recnd
    @13
    @54
    @61
    recnd
    negsubd
    eqcomd
    mpteq2dva
    wph
    vs
    @52
    @94
    @0
    wph
    vs
    @0
    @52
    cmpt
    vs
    @0
    @51
    cF
    cA
    cX
    caddc
    co
    #
    cB
    cX
    caddc
    co
    #
    cioo
    co
    #
    cres
    #
    cfv
    #
    cmpt
    @90
    wph
    vs
    @0
    @52
    @100
    @13
    @100
    @52
    @13
    @51
    @98
    wcel
    @100
    @52
    wceq
    @13
    @96
    @97
    @51
    wph
    @96
    cxr
    wcel
    @11
    wph
    @96
    wph
    cA
    cX
    @24
    fourierdlem78.x
    readdcld
    rexrd
    adantr
    wph
    @97
    cxr
    wcel
    @11
    wph
    @97
    wph
    cB
    cX
    @32
    fourierdlem78.x
    readdcld
    rexrd
    adantr
    @59
    @13
    @96
    cX
    cA
    caddc
    co
    #
    @51
    clt
    wph
    @96
    @101
    wceq
    @11
    wph
    cA
    cX
    wph
    cA
    @24
    recnd
    wph
    cX
    fourierdlem78.x
    recnd
    #
    addcomd
    adantr
    @13
    cA
    @2
    cX
    @25
    @21
    @58
    @36
    ltadd2dd
    eqbrtrd
    @13
    @51
    cX
    cB
    caddc
    co
    #
    @97
    clt
    @13
    @2
    cB
    cX
    @21
    @38
    @58
    @40
    ltadd2dd
    wph
    @103
    @97
    wceq
    @11
    wph
    cX
    cB
    @102
    wph
    cB
    @32
    recnd
    addcomd
    adantr
    breqtrd
    eliood
    #
    @51
    @98
    cF
    fvres
    syl
    eqcomd
    mpteq2dva
    wph
    @98
    @0
    @99
    cX
    vs
    @98
    cc
    wss
    wph
    @96
    @97
    ioosscn
    a1i
    fourierdlem78.fcn
    @0
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    #
    @102
    @104
    fourierdlem23
    eqeltrd
    wph
    cc0
    cA
    cle
    wbr
    #
    vs
    @0
    @94
    cmpt
    #
    @90
    wcel
    #
    wph
    @106
    wa
    #
    @107
    vs
    @0
    cY
    cneg
    #
    cmpt
    #
    @90
    @109
    vs
    @0
    @94
    @110
    @109
    @11
    wa
    #
    @54
    cY
    @112
    @53
    cY
    cW
    @112
    cc0
    cA
    @2
    @112
    0red
    wph
    @22
    @106
    @11
    @24
    ad2antrr
    @11
    @19
    @109
    @20
    adantl
    wph
    @106
    @11
    simplr
    wph
    @11
    @30
    @106
    @36
    adantlr
    lelttrd
    iftrued
    negeqd
    mpteq2dva
    wph
    @111
    @90
    wcel
    @106
    wph
    vs
    @0
    @110
    cc
    @105
    wph
    @110
    wph
    cY
    fourierdlem78.y
    renegcld
    recnd
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    #
    constcncfg
    adantr
    eqeltrd
    wph
    @106
    wn
    #
    wa
    #
    wph
    cB
    cc0
    cle
    wbr
    #
    @108
    wph
    @116
    simpl
    @117
    @118
    @63
    @117
    @118
    wn
    #
    wa
    #
    cA
    cB
    cc0
    wph
    @28
    @116
    @119
    wph
    cA
    @24
    rexrd
    ad2antrr
    wph
    @29
    @116
    @119
    @33
    ad2antrr
    @120
    0red
    @117
    cA
    cc0
    clt
    wbr
    #
    @119
    @117
    @121
    @116
    wph
    @116
    simpr
    @117
    cA
    cc0
    wph
    @22
    @116
    @24
    adantr
    @117
    0red
    ltnled
    mpbird
    adantr
    wph
    @119
    cc0
    cB
    clt
    wbr
    #
    @116
    wph
    @119
    wa
    #
    @122
    @119
    wph
    @119
    simpr
    @123
    cc0
    cB
    @123
    0red
    wph
    @37
    @119
    @32
    adantr
    ltnled
    mpbird
    adantlr
    eliood
    wph
    @64
    @116
    @119
    fourierdlem78.nxelab
    ad2antrr
    condan
    wph
    @118
    wa
    #
    @107
    vs
    @0
    cW
    cneg
    #
    cmpt
    #
    @90
    @124
    vs
    @0
    @94
    @125
    @124
    @11
    wa
    #
    @54
    cW
    @127
    @53
    cY
    cW
    @127
    @2
    cc0
    @11
    @19
    @124
    @20
    adantl
    #
    @127
    0red
    #
    @127
    @2
    cB
    cc0
    @128
    wph
    @37
    @118
    @11
    @32
    ad2antrr
    @129
    wph
    @11
    @39
    @118
    @40
    adantlr
    wph
    @118
    @11
    simplr
    ltletrd
    ltnsymd
    iffalsed
    negeqd
    mpteq2dva
    wph
    @126
    @90
    wcel
    @118
    wph
    vs
    @0
    @125
    cc
    @105
    wph
    cW
    wph
    cW
    fourierdlem78.w
    recnd
    negcld
    @115
    constcncfg
    adantr
    eqeltrd
    syl2anc
    pm2.61dan
    addcncf
    eqeltrd
    wph
    vs
    cc
    cc0
    csn
    #
    cdif
    #
    cc
    @0
    cc
    @91
    vs
    @131
    @91
    cmpt
    #
    @132
    eqid
    #
    wph
    c1
    cc
    wcel
    @132
    @131
    cc
    ccncf
    co
    wcel
    wph
    1cnd
    vs
    c1
    @132
    @133
    cdivcncf
    syl
    wph
    @2
    @131
    wcel
    #
    vs
    @0
    wral
    @0
    @131
    wss
    wph
    @134
    vs
    @0
    @13
    @2
    cc
    @130
    @93
    @13
    @50
    @2
    @130
    wcel
    @65
    vs
    cc0
    velsn
    sylnibr
    eldifd
    ralrimiva
    vs
    @0
    @131
    dfss3
    sylibr
    @115
    @13
    @91
    @13
    @2
    @21
    @66
    rereccld
    recnd
    cncfmptssg
    mulcncf
    eqeltrd
    wph
    vs
    @0
    @48
    cmpt
    vs
    @0
    @2
    c1
    @71
    cdiv
    co
    cmul
    co
    #
    cmpt
    #
    @90
    wph
    vs
    @0
    @48
    @135
    @13
    @48
    @73
    @72
    @135
    @80
    @13
    @50
    c1
    @72
    @65
    iffalsed
    #
    @13
    @2
    @71
    @93
    @13
    @71
    @76
    recnd
    @78
    divrecd
    #
    3eqtrd
    mpteq2dva
    wph
    @136
    vs
    @0
    @73
    cmpt
    @90
    wph
    vs
    @0
    @135
    @73
    @13
    @73
    @72
    @135
    @137
    @138
    eqtr2d
    mpteq2dva
    wph
    vs
    @9
    cc
    @0
    cc
    @73
    vs
    @9
    @73
    cmpt
    #
    @139
    eqid
    #
    wph
    @9
    cr
    ccncf
    co
    #
    @9
    cc
    ccncf
    co
    #
    @139
    @89
    @113
    @141
    @142
    wss
    ax-resscn
    @114
    @9
    cr
    cc
    cncfss
    mp2an
    @139
    @141
    wcel
    wph
    vs
    @139
    @140
    fourierdlem62
    a1i
    sseldi
    @44
    @115
    @13
    @73
    @79
    recnd
    cncfmptssg
    eqeltrd
    eqeltrd
    mulcncf
    eqeltrd
    wph
    vs
    @0
    @4
    cmpt
    vs
    @0
    @86
    cmpt
    @90
    wph
    vs
    @0
    @4
    @86
    @88
    mpteq2dva
    wph
    vs
    @85
    csin
    @0
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
    vs
    @84
    @2
    @0
    wph
    vs
    @0
    @84
    cc
    @105
    wph
    @84
    wph
    cN
    @83
    fourierdlem78.n
    @83
    cr
    wcel
    wph
    halfre
    a1i
    readdcld
    recnd
    @115
    constcncfg
    wph
    vs
    @0
    cc
    @105
    @115
    idcncfg
    mulcncf
    cncfmpt1f
    eqeltrd
    mulcncf
    @0
    cc
    cr
    @6
    cncffvrn
    syl2anc
    mpbird
    eqeltrd
end
