include "cpi.mm"
include "cneg.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "pire.mm"
include "a1i.mm"
include "renegcld.mm"
include "crn.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cfzo.mm"
include "wral.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "frn.mm"
include "3syl.mm"
include "sseldd.mm"
include "fourierdlem14.mm"
include "cicc.mm"
include "cc.mm"
include "cpnf.mm"
include "cioo.mm"
include "cres.mm"
include "ioossre.mm"
include "fssresd.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "cxr.mm"
include "pnfxr.mm"
include "ltpnfd.mm"
include "lptioo1cn.mm"
include "limcrecl.mm"
include "cmnf.mm"
include "mnfxr.mm"
include "mnfltd.mm"
include "lptioo2cn.mm"
include "fourierdlem55.mm"
include "ffvelrnda.mm"
include "fourierdlem5.mm"
include "remulcld.mm"
include "recnd.mm"
include "fmptd.mm"
include "ccncf.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "adantr.mm"
include "fourierdlem15.mm"
include "elfzofz.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "fzofzp1.mm"
include "fourierdlem12.mm"
include "addid2d.mm"
include "readdcld.mm"
include "iccssred.mm"
include "resubcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "npcand.mm"
include "eqtrd.mm"
include "cmpt.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simpr.mm"
include "fveq2d.mm"
include "fvmptd.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "mtbird.mm"
include "0red.mm"
include "eqeltrd.mm"
include "eliooshift.mm"
include "reseq2d.mm"
include "3eltr4d.mm"
include "fourierdlem78.mm"
include "sseldi.mm"
include "climc.mm"
include "renegcli.mm"
include "rexri.mm"
include "simplr.mm"
include "fourierdlem8.mm"
include "ioossicc.mm"
include "sseli.mm"
include "fourierdlem9.mm"
include "ad2antrr.mm"
include "fourierdlem43.mm"
include "fourierdlem18.mm"
include "cncff.mm"
include "fssd.mm"
include "fourierdlem75.mm"
include "syl5ss.mm"
include "feqresmpt.mm"
include "eleqtrd.mm"
include "limcresi.mm"
include "fourierdlem62.mm"
include "cnlimci.mm"
include "mullimc.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "eqtr2d.mm"
include "fourierdlem74.mm"
include "fourierdlem69.mm"

theorem fourierdlem88
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem88.1: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( -u _pi + X ) /\ ( p ` m ) = ( _pi + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem88.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem88.x: |- ( ph -> X e. ran V )
  assume fourierdlem88.y: |- ( ph -> Y e. ( ( F |` ( X (,) +oo ) ) limCC X ) )
  assume fourierdlem88.w: |- ( ph -> W e. ( ( F |` ( -oo (,) X ) ) limCC X ) )
  assume fourierdlem88.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem88.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem88.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem88.n: |- ( ph -> N e. RR )
  assume fourierdlem88.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( N + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem88.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )
  assume fourierdlem88.m: |- ( ph -> M e. NN )
  assume fourierdlem88.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem88.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) e. ( ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem88.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` i ) ) )
  assume fourierdlem88.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` ( i + 1 ) ) ) )
  assume fourierdlem88.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )
  assume fourierdlem88.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = -u _pi /\ ( p ` m ) = _pi ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem88.i: |- I = ( RR _D F )
  assume fourierdlem88.ifn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( I |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) : ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) --> RR )
  assume fourierdlem88.c: |- ( ph -> C e. ( ( I |` ( -oo (,) X ) ) limCC X ) )
  assume fourierdlem88.d: |- ( ph -> D e. ( ( I |` ( X (,) +oo ) ) limCC X ) )

  disjoint C s
  disjoint D s
  disjoint F s
  disjoint G i
  disjoint G s
  disjoint i s
  disjoint H s
  disjoint K s
  disjoint L s
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint M s
  disjoint N s
  disjoint Q i
  disjoint Q p
  disjoint Q s
  disjoint R s
  disjoint S s
  disjoint V i
  disjoint V p
  disjoint V s
  disjoint W s
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X s
  disjoint Y s
  disjoint i ph
  disjoint ph s
  disjoint M j
  disjoint i j
  disjoint V j
  disjoint X j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> G e. L^1 )

  proof
    wph
    cpi
    cneg
    #
    cpi
    cO
    cQ
    vi
    cv
    #
    cV
    cfv
    #
    cX
    wceq
    cD
    cR
    @2
    cX
    clt
    wbr
    cW
    cY
    cif
    cmin
    co
    @1
    cQ
    cfv
    #
    cdiv
    co
    cif
    #
    @3
    cK
    cfv
    #
    cmul
    co
    #
    @3
    cS
    cfv
    #
    cmul
    co
    #
    vi
    vm
    cG
    @1
    c1
    caddc
    co
    #
    cV
    cfv
    #
    cX
    wceq
    cC
    cL
    @10
    cX
    clt
    wbr
    cW
    cY
    cif
    cmin
    co
    @9
    cQ
    cfv
    #
    cdiv
    co
    cif
    #
    @11
    cK
    cfv
    #
    cmul
    co
    #
    @11
    cS
    cfv
    #
    cmul
    co
    #
    cM
    vp
    fourierdlem88.o
    fourierdlem88.m
    wph
    @0
    cpi
    cP
    cQ
    vi
    vm
    cM
    cO
    cV
    cX
    vp
    wph
    cpi
    cpi
    cr
    wcel
    #
    wph
    pire
    a1i
    #
    renegcld
    @18
    wph
    cV
    crn
    #
    cr
    cX
    wph
    cV
    cr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    wcel
    #
    @20
    cr
    cV
    wf
    @19
    cr
    wss
    wph
    @21
    cc0
    cV
    cfv
    @0
    cX
    caddc
    co
    #
    wceq
    cM
    cV
    cfv
    cpi
    cX
    caddc
    co
    #
    wceq
    wa
    @2
    @10
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    wa
    #
    wph
    cV
    cM
    cP
    cfv
    wcel
    #
    @21
    @25
    wa
    #
    fourierdlem88.v
    wph
    cM
    cn
    wcel
    @26
    @27
    wb
    fourierdlem88.m
    @22
    @23
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem88.1
    fourierdlem2
    syl
    mpbid
    simpld
    cV
    cr
    @20
    elmapi
    @20
    cr
    cV
    frn
    3syl
    fourierdlem88.x
    sseldd
    #
    fourierdlem88.1
    fourierdlem88.o
    fourierdlem88.m
    fourierdlem88.v
    fourierdlem88.q
    fourierdlem14
    #
    wph
    vs
    @0
    cpi
    cicc
    co
    #
    vs
    cv
    #
    cU
    cfv
    #
    @31
    cS
    cfv
    #
    cmul
    co
    #
    cc
    cG
    wph
    @31
    @30
    wcel
    #
    wa
    #
    @34
    @36
    @32
    @33
    wph
    @30
    cr
    @31
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
    fourierdlem88.f
    @28
    wph
    cX
    cpnf
    cioo
    co
    #
    cX
    cF
    @37
    cres
    cY
    wph
    cr
    cr
    @37
    cF
    fourierdlem88.f
    @37
    cr
    wss
    wph
    cX
    cpnf
    ioossre
    a1i
    #
    fssresd
    wph
    @37
    cr
    cc
    @38
    ax-resscn
    syl6ss
    wph
    cX
    cpnf
    ccnfld
    ctopn
    cfv
    #
    @39
    eqid
    #
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    @28
    wph
    cX
    @28
    ltpnfd
    lptioo1cn
    fourierdlem88.y
    limcrecl
    #
    wph
    cmnf
    cX
    cioo
    co
    #
    cX
    cF
    @42
    cres
    cW
    wph
    cr
    cr
    @42
    cF
    fourierdlem88.f
    @42
    cr
    wss
    wph
    cmnf
    cX
    ioossre
    a1i
    #
    fssresd
    wph
    @42
    cr
    cc
    @43
    ax-resscn
    syl6ss
    wph
    cmnf
    cX
    @39
    @40
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    @28
    wph
    cX
    @28
    mnfltd
    lptioo2cn
    fourierdlem88.w
    limcrecl
    #
    fourierdlem88.h
    fourierdlem88.k
    fourierdlem88.u
    fourierdlem55
    ffvelrnda
    wph
    @30
    cr
    @31
    cS
    wph
    cN
    cr
    wcel
    #
    @30
    cr
    cS
    wf
    #
    fourierdlem88.n
    vs
    cS
    cN
    fourierdlem88.s
    fourierdlem5
    syl
    ffvelrnda
    remulcld
    #
    recnd
    fourierdlem88.g
    fmptd
    wph
    @1
    @24
    wcel
    #
    wa
    #
    @3
    @11
    cioo
    co
    #
    cr
    ccncf
    co
    #
    @50
    cc
    ccncf
    co
    #
    cG
    @50
    cres
    #
    cr
    cc
    wss
    #
    cc
    cc
    wss
    @51
    @52
    wss
    ax-resscn
    cc
    ssid
    @50
    cr
    cc
    cncfss
    mp2an
    @49
    @3
    @11
    cS
    cU
    cF
    cG
    cH
    cK
    cN
    cW
    cX
    cY
    vs
    wph
    cr
    cr
    cF
    wf
    @48
    fourierdlem88.f
    adantr
    @49
    @20
    @30
    @1
    cQ
    wph
    @20
    @30
    cQ
    wf
    #
    @48
    wph
    @0
    cpi
    cO
    cQ
    vi
    vm
    cM
    vp
    fourierdlem88.o
    fourierdlem88.m
    @29
    fourierdlem15
    adantr
    #
    @48
    @1
    @20
    wcel
    #
    wph
    @1
    cc0
    cM
    elfzofz
    adantl
    #
    ffvelrnd
    #
    @49
    @20
    @30
    @9
    cQ
    @56
    @48
    @9
    @20
    wcel
    wph
    cc0
    cM
    @1
    fzofzp1
    adantl
    #
    ffvelrnd
    #
    wph
    cX
    cr
    wcel
    @48
    @28
    adantr
    #
    @49
    cc0
    @50
    wcel
    cc0
    cX
    caddc
    co
    #
    @3
    cX
    caddc
    co
    #
    @11
    cX
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @49
    @67
    cX
    @2
    @10
    cioo
    co
    #
    wcel
    wph
    @22
    @23
    cP
    cV
    vi
    vm
    cM
    cX
    vp
    fourierdlem88.1
    fourierdlem88.m
    fourierdlem88.v
    fourierdlem88.x
    fourierdlem12
    @49
    @63
    cX
    @66
    @68
    @49
    cX
    @49
    cX
    @62
    recnd
    #
    addid2d
    @49
    @64
    @2
    @65
    @10
    cioo
    @49
    @64
    @2
    cX
    cmin
    co
    #
    cX
    caddc
    co
    @2
    @49
    @3
    @70
    cX
    caddc
    @49
    @57
    @70
    cr
    wcel
    @3
    @70
    wceq
    @58
    @49
    @2
    cX
    @49
    @22
    @23
    cicc
    co
    #
    cr
    @2
    @49
    @22
    @23
    @49
    @0
    cX
    @49
    cpi
    @17
    @49
    pire
    a1i
    #
    renegcld
    @62
    readdcld
    @49
    cpi
    cX
    @72
    @62
    readdcld
    iccssred
    #
    @49
    @20
    @71
    @1
    cV
    wph
    @20
    @71
    cV
    wf
    @48
    wph
    @22
    @23
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem88.1
    fourierdlem88.m
    fourierdlem88.v
    fourierdlem15
    adantr
    #
    @58
    ffvelrnd
    sseldd
    #
    @62
    resubcld
    #
    vi
    @20
    @70
    cr
    cQ
    fourierdlem88.q
    fvmpt2
    syl2anc
    #
    oveq1d
    @49
    @2
    cX
    @49
    @2
    @75
    recnd
    @69
    npcand
    eqtrd
    @49
    @65
    @10
    cX
    cmin
    co
    #
    cX
    caddc
    co
    @10
    @49
    @11
    @78
    cX
    caddc
    @49
    vj
    @9
    vj
    cv
    #
    cV
    cfv
    #
    cX
    cmin
    co
    #
    @78
    @20
    cQ
    cr
    cQ
    vj
    @20
    @81
    cmpt
    #
    wceq
    @49
    cQ
    vi
    @20
    @70
    cmpt
    @82
    fourierdlem88.q
    vi
    vj
    @20
    @70
    @81
    @1
    @79
    wceq
    @2
    @80
    cX
    cmin
    @1
    @79
    cV
    fveq2
    oveq1d
    cbvmptv
    eqtri
    a1i
    @49
    @79
    @9
    wceq
    #
    wa
    #
    @80
    @10
    cX
    cmin
    @84
    @79
    @9
    cV
    @49
    @83
    simpr
    fveq2d
    oveq1d
    @60
    @49
    @10
    cX
    @49
    @71
    cr
    @10
    @73
    @49
    @20
    @71
    @9
    cV
    @74
    @60
    ffvelrnd
    sseldd
    #
    @62
    resubcld
    #
    fvmptd
    #
    oveq1d
    @49
    @10
    cX
    @49
    @10
    @85
    recnd
    @69
    npcand
    eqtrd
    oveq12d
    #
    eleq12d
    mtbird
    @49
    cc0
    @3
    @11
    cX
    @49
    0red
    @49
    @3
    @70
    cr
    @77
    @76
    eqeltrd
    @49
    @11
    @78
    cr
    @87
    @86
    eqeltrd
    @62
    eliooshift
    mtbird
    @49
    cF
    @68
    cres
    @68
    cc
    ccncf
    co
    cF
    @66
    cres
    @66
    cc
    ccncf
    co
    fourierdlem88.fcn
    @49
    @66
    @68
    cF
    @88
    reseq2d
    @49
    @66
    @68
    cc
    ccncf
    @88
    oveq1d
    3eltr4d
    wph
    cY
    cr
    wcel
    @48
    @41
    adantr
    wph
    cW
    cr
    wcel
    @48
    @44
    adantr
    fourierdlem88.h
    fourierdlem88.k
    fourierdlem88.u
    wph
    @45
    @48
    fourierdlem88.n
    adantr
    fourierdlem88.s
    fourierdlem88.g
    fourierdlem78
    sseldi
    @49
    @8
    vs
    @50
    @34
    cmpt
    #
    @3
    climc
    co
    @53
    @3
    climc
    co
    @49
    vs
    @50
    @32
    @33
    @3
    vs
    @50
    @32
    cmpt
    #
    vs
    @50
    @33
    cmpt
    #
    @89
    @6
    @7
    @90
    eqid
    #
    @91
    eqid
    #
    @89
    eqid
    #
    @49
    @31
    @50
    wcel
    #
    wa
    #
    @32
    @96
    @32
    @31
    cH
    cfv
    #
    @31
    cK
    cfv
    #
    cmul
    co
    #
    cr
    @96
    @35
    @99
    cr
    wcel
    @32
    @99
    wceq
    @96
    @3
    @11
    cicc
    co
    #
    @30
    @31
    @96
    @0
    cpi
    cQ
    @1
    cM
    @0
    cxr
    wcel
    #
    @96
    @0
    cpi
    pire
    renegcli
    rexri
    #
    a1i
    cpi
    cxr
    wcel
    #
    @96
    cpi
    pire
    rexri
    #
    a1i
    @49
    @55
    @95
    @56
    adantr
    wph
    @48
    @95
    simplr
    fourierdlem8
    @95
    @31
    @100
    wcel
    @49
    @50
    @100
    @31
    @3
    @11
    ioossicc
    #
    sseli
    adantl
    sseldd
    #
    @96
    @97
    @98
    @96
    @30
    cr
    @31
    cH
    wph
    @30
    cr
    cH
    wf
    #
    @48
    @95
    wph
    cF
    cH
    cW
    cX
    cY
    vs
    fourierdlem88.f
    @28
    @41
    @44
    fourierdlem88.h
    fourierdlem9
    #
    ad2antrr
    @106
    ffvelrnd
    #
    @96
    @30
    cr
    @31
    cK
    @30
    cr
    cK
    wf
    #
    @96
    cK
    vs
    fourierdlem88.k
    fourierdlem43
    #
    a1i
    @106
    ffvelrnd
    #
    remulcld
    #
    vs
    @30
    @99
    cr
    cU
    fourierdlem88.u
    fvmpt2
    syl2anc
    #
    @113
    eqeltrd
    #
    recnd
    #
    @96
    @33
    @96
    @30
    cr
    @31
    cS
    @49
    @46
    @95
    wph
    @46
    @48
    wph
    cS
    @30
    cr
    ccncf
    co
    #
    wcel
    #
    @46
    wph
    cS
    cN
    vs
    fourierdlem88.n
    fourierdlem88.s
    fourierdlem18
    #
    @30
    cr
    cS
    cncff
    syl
    adantr
    #
    adantr
    @106
    ffvelrnd
    #
    recnd
    #
    @49
    @6
    vs
    @50
    @99
    cmpt
    #
    @3
    climc
    co
    @90
    @3
    climc
    co
    @49
    vs
    @50
    @97
    @98
    @3
    vs
    @50
    @97
    cmpt
    #
    vs
    @50
    @98
    cmpt
    #
    @123
    @4
    @5
    @124
    eqid
    #
    @125
    eqid
    #
    @123
    eqid
    #
    @96
    @97
    @109
    recnd
    #
    @96
    @98
    @112
    recnd
    #
    @49
    @4
    cH
    @50
    cres
    #
    @3
    climc
    co
    @124
    @3
    climc
    co
    wph
    @4
    cP
    cQ
    cR
    vi
    vm
    cD
    cF
    cI
    cH
    cM
    cO
    cV
    cW
    cX
    cY
    vs
    vp
    @28
    fourierdlem88.1
    fourierdlem88.f
    fourierdlem88.x
    fourierdlem88.y
    @44
    fourierdlem88.h
    fourierdlem88.m
    fourierdlem88.v
    fourierdlem88.r
    fourierdlem88.q
    fourierdlem88.o
    fourierdlem88.i
    @49
    @68
    cr
    cc
    cI
    @68
    cres
    fourierdlem88.ifn
    @54
    @49
    ax-resscn
    a1i
    fssd
    fourierdlem88.d
    @4
    eqid
    fourierdlem75
    @49
    @131
    @124
    @3
    climc
    @49
    vs
    @30
    cr
    @50
    cH
    wph
    @107
    @48
    @108
    adantr
    @49
    @50
    @100
    @30
    @105
    @49
    @0
    cpi
    cQ
    @1
    cM
    @101
    @49
    @102
    a1i
    @103
    @49
    @104
    a1i
    @56
    wph
    @48
    simpr
    fourierdlem8
    syl5ss
    #
    feqresmpt
    #
    oveq1d
    eleqtrd
    @49
    @5
    cK
    @50
    cres
    #
    @3
    climc
    co
    #
    @125
    @3
    climc
    co
    @49
    cK
    @3
    climc
    co
    @135
    @5
    @3
    @50
    cK
    limcresi
    @49
    @30
    @3
    cr
    cK
    cK
    @117
    wcel
    @49
    vs
    cK
    fourierdlem88.k
    fourierdlem62
    a1i
    #
    @59
    cnlimci
    sseldi
    @49
    @134
    @125
    @3
    climc
    @49
    vs
    @30
    cr
    @50
    cK
    @110
    @49
    @111
    a1i
    @132
    feqresmpt
    #
    oveq1d
    eleqtrd
    mullimc
    @49
    @123
    @90
    @3
    climc
    @49
    vs
    @50
    @99
    @32
    @96
    @32
    @99
    @114
    eqcomd
    mpteq2dva
    #
    oveq1d
    eleqtrd
    @49
    @7
    cS
    @50
    cres
    #
    @3
    climc
    co
    #
    @91
    @3
    climc
    co
    @49
    cS
    @3
    climc
    co
    @140
    @7
    @3
    @50
    cS
    limcresi
    @49
    @30
    @3
    cr
    cS
    wph
    @118
    @48
    @119
    adantr
    #
    @59
    cnlimci
    sseldi
    @49
    @139
    @91
    @3
    climc
    @49
    vs
    @30
    cr
    @50
    cS
    @120
    @132
    feqresmpt
    #
    oveq1d
    eleqtrd
    mullimc
    @49
    @89
    @53
    @3
    climc
    @49
    @53
    vs
    @50
    @31
    cG
    cfv
    #
    cmpt
    @89
    @49
    vs
    @30
    cr
    @50
    cG
    wph
    @30
    cr
    cG
    wf
    @48
    wph
    vs
    @30
    @34
    cr
    cG
    @47
    fourierdlem88.g
    fmptd
    adantr
    @132
    feqresmpt
    @49
    vs
    @50
    @143
    @34
    @96
    @35
    @34
    cr
    wcel
    @143
    @34
    wceq
    @106
    @96
    @32
    @33
    @115
    @121
    remulcld
    vs
    @30
    @34
    cr
    cG
    fourierdlem88.g
    fvmpt2
    syl2anc
    mpteq2dva
    eqtr2d
    #
    oveq1d
    eleqtrd
    @49
    @16
    @89
    @11
    climc
    co
    @53
    @11
    climc
    co
    @49
    vs
    @50
    @32
    @33
    @11
    @90
    @91
    @89
    @14
    @15
    @92
    @93
    @94
    @116
    @122
    @49
    @14
    @123
    @11
    climc
    co
    @90
    @11
    climc
    co
    @49
    vs
    @50
    @97
    @98
    @11
    @124
    @125
    @123
    @12
    @13
    @126
    @127
    @128
    @129
    @130
    @49
    @12
    @131
    @11
    climc
    co
    @124
    @11
    climc
    co
    wph
    @12
    cP
    cQ
    cL
    vi
    vm
    cC
    cF
    cI
    cH
    cM
    cO
    cV
    cW
    cX
    cY
    vs
    vp
    @28
    fourierdlem88.1
    fourierdlem88.f
    fourierdlem88.x
    @41
    fourierdlem88.w
    fourierdlem88.h
    fourierdlem88.m
    fourierdlem88.v
    fourierdlem88.l
    fourierdlem88.q
    fourierdlem88.o
    fourierdlem88.i
    fourierdlem88.ifn
    fourierdlem88.c
    @12
    eqid
    fourierdlem74
    @49
    @131
    @124
    @11
    climc
    @133
    oveq1d
    eleqtrd
    @49
    @13
    @134
    @11
    climc
    co
    #
    @125
    @11
    climc
    co
    @49
    cK
    @11
    climc
    co
    @145
    @13
    @11
    @50
    cK
    limcresi
    @49
    @30
    @11
    cr
    cK
    @136
    @61
    cnlimci
    sseldi
    @49
    @134
    @125
    @11
    climc
    @137
    oveq1d
    eleqtrd
    mullimc
    @49
    @123
    @90
    @11
    climc
    @138
    oveq1d
    eleqtrd
    @49
    @15
    @139
    @11
    climc
    co
    #
    @91
    @11
    climc
    co
    @49
    cS
    @11
    climc
    co
    @146
    @15
    @11
    @50
    cS
    limcresi
    @49
    @30
    @11
    cr
    cS
    @141
    @61
    cnlimci
    sseldi
    @49
    @139
    @91
    @11
    climc
    @142
    oveq1d
    eleqtrd
    mullimc
    @49
    @89
    @53
    @11
    climc
    @144
    oveq1d
    eleqtrd
    fourierdlem69
end
