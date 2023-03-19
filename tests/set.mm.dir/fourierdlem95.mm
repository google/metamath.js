include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "citg.mm"
include "cpi.mm"
include "cmul.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "cneg.mm"
include "cicc.mm"
include "wss.mm"
include "csn.mm"
include "difss2d.mm"
include "adantr.mm"
include "sselda.mm"
include "wf.mm"
include "cpnf.mm"
include "cioo.mm"
include "cres.mm"
include "ioossre.mm"
include "a1i.mm"
include "fssresd.mm"
include "cc.mm"
include "ioosscn.mm"
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
include "nnred.mm"
include "fourierdlem67.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "cvol.mm"
include "cdm.mm"
include "cmpt.mm"
include "cibl.mm"
include "feqmptd.mm"
include "cfz.mm"
include "c1.mm"
include "cfzo.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "crn.mm"
include "climc.mm"
include "ccncf.mm"
include "adantlr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "fourierdlem88.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "itgrecl.mm"
include "pire.mm"
include "wne.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "redivcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "recnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divrecd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cdif.mm"
include "fourierdlem66.mm"
include "itgeq2dv.mm"
include "difss.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sstri.mm"
include "sseldi.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "ifcld.mm"
include "resubcld.mm"
include "dirkerre.mm"
include "remulcld.mm"
include "picn.mm"
include "div23d.mm"
include "divrec2d.mm"
include "3eqtr3rd.mm"
include "dividi.mm"
include "mulid2d.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "reccld.mm"
include "iblmulc2.mm"
include "eqeltrd.mm"
include "itgmulc2.mm"
include "itgcl.mm"
include "divcan3d.mm"
include "3eqtrd.mm"
include "sseli.mm"
include "sylan2.mm"
include "adantll.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "sylancl.mm"
include "dirkerf.mm"
include "dirkercncf.mm"
include "cncfmptssg.mm"
include "sseldd.mm"
include "adantl.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "itgadd.mm"
include "subdird.mm"
include "mulcld.mm"
include "npcand.mm"
include "eqtr3d.mm"

theorem fourierdlem95
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
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
  assume fourierdlem95.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem95.xre: |- ( ph -> X e. RR )
  assume fourierdlem95.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( -u _pi + X ) /\ ( p ` m ) = ( _pi + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem95.m: |- ( ph -> M e. NN )
  assume fourierdlem95.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem95.x: |- ( ph -> X e. ran V )
  assume fourierdlem95.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) e. ( ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem95.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` i ) ) )
  assume fourierdlem95.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` ( i + 1 ) ) ) )
  assume fourierdlem95.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )
  assume fourierdlem95.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem95.u: |- U = ( s e. ( -u _pi [,] _pi ) |-> ( ( H ` s ) x. ( K ` s ) ) )
  assume fourierdlem95.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) )
  assume fourierdlem95.g: |- G = ( s e. ( -u _pi [,] _pi ) |-> ( ( U ` s ) x. ( S ` s ) ) )
  assume fourierdlem95.i: |- I = ( RR _D F )
  assume fourierdlem95.ifn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( I |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) : ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) --> RR )
  assume fourierdlem95.b: |- ( ph -> B e. ( ( I |` ( -oo (,) X ) ) limCC X ) )
  assume fourierdlem95.c: |- ( ph -> C e. ( ( I |` ( X (,) +oo ) ) limCC X ) )
  assume fourierdlem95.y: |- ( ph -> Y e. ( ( F |` ( X (,) +oo ) ) limCC X ) )
  assume fourierdlem95.w: |- ( ph -> W e. ( ( F |` ( -oo (,) X ) ) limCC X ) )
  assume fourierdlem95.admvol: |- ( ph -> A e. dom vol )
  assume fourierdlem95.ass: |- ( ph -> A C_ ( ( -u _pi [,] _pi ) \ { 0 } ) )
  assume fourierlemenplusacver2eqitgdirker.e: |- E = ( n e. NN |-> ( S. A ( G ` s ) _d s / _pi ) )
  assume fourierdlem95.d: |- D = ( n e. NN |-> ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )
  assume fourierdlem95.o: |- ( ph -> O e. RR )
  assume fourierdlem95.ifeqo: |- ( ( ph /\ s e. A ) -> if ( 0 < s , Y , W ) = O )
  assume fourierdlem95.itgdirker: |- ( ( ph /\ n e. NN ) -> S. A ( ( D ` n ) ` s ) _d s = ( 1 / 2 ) )

  disjoint A s
  disjoint B s
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
  disjoint M p
  disjoint i p
  disjoint M m
  disjoint i m
  disjoint m p
  disjoint M s
  disjoint O s
  disjoint R s
  disjoint S s
  disjoint V i
  disjoint V p
  disjoint V s
  disjoint W s
  disjoint X i
  disjoint X p
  disjoint X m
  disjoint X s
  disjoint Y s
  disjoint i n
  disjoint n s
  disjoint i ph
  disjoint ph s
  disjoint M j
  disjoint i j
  disjoint j p
  disjoint j s
  disjoint V j
  disjoint X j
  disjoint k x
  assert |- ( ( ph /\ n e. NN ) -> ( ( E ` n ) + ( O / 2 ) ) = S. A ( ( F ` ( X + s ) ) x. ( ( D ` n ) ` s ) ) _d s )

  proof
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    @0
    cE
    cfv
    #
    cO
    c2
    cdiv
    co
    #
    caddc
    co
    vs
    cA
    vs
    cv
    #
    cG
    cfv
    #
    citg
    #
    cpi
    cdiv
    co
    #
    cO
    vs
    cA
    @5
    @0
    cD
    cfv
    #
    cfv
    #
    citg
    #
    cmul
    co
    #
    caddc
    co
    vs
    cA
    cX
    @5
    caddc
    co
    #
    cF
    cfv
    #
    cc0
    @5
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
    @10
    cmul
    co
    #
    citg
    #
    vs
    cA
    cO
    @10
    cmul
    co
    #
    citg
    #
    caddc
    co
    #
    vs
    cA
    @14
    @10
    cmul
    co
    #
    citg
    #
    @2
    @3
    @8
    @4
    @12
    caddc
    @2
    @1
    @8
    cr
    wcel
    @3
    @8
    wceq
    wph
    @1
    simpr
    #
    @2
    @7
    cpi
    @2
    vs
    cA
    @6
    @2
    @5
    cA
    wcel
    #
    @5
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wcel
    #
    @6
    cr
    wcel
    @2
    cA
    @28
    @5
    wph
    cA
    @28
    wss
    @1
    wph
    cA
    @28
    cc0
    csn
    #
    fourierdlem95.ass
    difss2d
    adantr
    #
    sselda
    @2
    @28
    cr
    @5
    cG
    @2
    cS
    cU
    cF
    cG
    cH
    cK
    @0
    cW
    cX
    cY
    vs
    wph
    cr
    cr
    cF
    wf
    #
    @1
    fourierdlem95.f
    adantr
    #
    wph
    cX
    cr
    wcel
    #
    @1
    fourierdlem95.xre
    adantr
    wph
    cY
    cr
    wcel
    @1
    wph
    cX
    cpnf
    cioo
    co
    #
    cX
    cF
    @35
    cres
    #
    cY
    wph
    cr
    cr
    @35
    cF
    fourierdlem95.f
    @35
    cr
    wss
    wph
    cX
    cpnf
    ioossre
    a1i
    fssresd
    @35
    cc
    wss
    wph
    cX
    cpnf
    ioosscn
    a1i
    wph
    cX
    cpnf
    ccnfld
    ctopn
    cfv
    #
    @37
    eqid
    #
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    fourierdlem95.xre
    wph
    cX
    fourierdlem95.xre
    ltpnfd
    lptioo1cn
    fourierdlem95.y
    limcrecl
    #
    adantr
    wph
    cW
    cr
    wcel
    @1
    wph
    cmnf
    cX
    cioo
    co
    #
    cX
    cF
    @40
    cres
    #
    cW
    wph
    cr
    cr
    @40
    cF
    fourierdlem95.f
    @40
    cr
    wss
    wph
    cmnf
    cX
    ioossre
    a1i
    fssresd
    @40
    cc
    wss
    wph
    cmnf
    cX
    ioosscn
    a1i
    wph
    cmnf
    cX
    @37
    @38
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    fourierdlem95.xre
    wph
    cX
    fourierdlem95.xre
    mnfltd
    lptioo2cn
    fourierdlem95.w
    limcrecl
    #
    adantr
    fourierdlem95.h
    fourierdlem95.k
    fourierdlem95.u
    @2
    @0
    @25
    nnred
    #
    fourierdlem95.s
    fourierdlem95.g
    fourierdlem67
    #
    ffvelrnda
    #
    syldan
    #
    @2
    vs
    cA
    @28
    @6
    cr
    @31
    wph
    cA
    cvol
    cdm
    wcel
    @1
    fourierdlem95.admvol
    adantr
    #
    @45
    @2
    cG
    vs
    @28
    @6
    cmpt
    cibl
    @2
    vs
    @28
    cr
    cG
    @44
    feqmptd
    @2
    cB
    cC
    cP
    vj
    cc0
    cM
    cfz
    co
    #
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
    cmpt
    cR
    cS
    cU
    vi
    vm
    cF
    cG
    cH
    cI
    cK
    cL
    cM
    @0
    vm
    cn
    cc0
    vp
    cv
    #
    cfv
    @27
    wceq
    vm
    cv
    #
    @52
    cfv
    cpi
    wceq
    wa
    vi
    cv
    #
    @52
    cfv
    @54
    c1
    caddc
    co
    #
    @52
    cfv
    clt
    wbr
    vi
    cc0
    @53
    cfzo
    co
    wral
    wa
    vp
    cr
    cc0
    @53
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    cV
    cW
    cX
    cY
    vs
    vp
    fourierdlem95.p
    @33
    wph
    cX
    cV
    crn
    wcel
    @1
    fourierdlem95.x
    adantr
    wph
    cY
    @36
    cX
    climc
    co
    wcel
    @1
    fourierdlem95.y
    adantr
    wph
    cW
    @41
    cX
    climc
    co
    wcel
    @1
    fourierdlem95.w
    adantr
    fourierdlem95.h
    fourierdlem95.k
    fourierdlem95.u
    @43
    fourierdlem95.s
    fourierdlem95.g
    wph
    cM
    cn
    wcel
    @1
    fourierdlem95.m
    adantr
    wph
    cV
    cM
    cP
    cfv
    wcel
    @1
    fourierdlem95.v
    adantr
    wph
    @54
    cc0
    cM
    cfzo
    co
    wcel
    #
    cF
    @54
    cV
    cfv
    #
    @55
    cV
    cfv
    #
    cioo
    co
    #
    cres
    #
    @60
    cc
    ccncf
    co
    wcel
    @1
    fourierdlem95.fcn
    adantlr
    wph
    @57
    cR
    @61
    @58
    climc
    co
    wcel
    @1
    fourierdlem95.r
    adantlr
    wph
    @57
    cL
    @61
    @59
    climc
    co
    wcel
    @1
    fourierdlem95.l
    adantlr
    vj
    vi
    @48
    @51
    @58
    cX
    cmin
    co
    @49
    @54
    wceq
    @50
    @58
    cX
    cmin
    @49
    @54
    cV
    fveq2
    oveq1d
    cbvmptv
    @56
    eqid
    fourierdlem95.i
    wph
    @57
    @60
    cr
    cI
    @60
    cres
    wf
    @1
    fourierdlem95.ifn
    adantlr
    wph
    cB
    cI
    @40
    cres
    cX
    climc
    co
    wcel
    @1
    fourierdlem95.b
    adantr
    wph
    cC
    cI
    @35
    cres
    cX
    climc
    co
    wcel
    @1
    fourierdlem95.c
    adantr
    fourierdlem88
    eqeltrrd
    iblss
    #
    itgrecl
    cpi
    cr
    wcel
    #
    @2
    pire
    a1i
    #
    cpi
    cc0
    wne
    #
    @2
    cpi
    pire
    pipos
    gt0ne0ii
    #
    a1i
    #
    redivcld
    vn
    cn
    @8
    cr
    cE
    fourierlemenplusacver2eqitgdirker.e
    fvmpt2
    syl2anc
    @2
    @4
    cO
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @12
    wph
    @4
    @69
    wceq
    @1
    wph
    cO
    c2
    wph
    cO
    fourierdlem95.o
    recnd
    #
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divrecd
    adantr
    @2
    @68
    @11
    cO
    cmul
    @2
    @11
    @68
    fourierdlem95.itgdirker
    eqcomd
    oveq2d
    eqtrd
    oveq12d
    @2
    @8
    @19
    @12
    @21
    caddc
    @2
    @8
    vs
    cA
    cpi
    @18
    cmul
    co
    #
    citg
    #
    cpi
    cdiv
    co
    cpi
    @19
    cmul
    co
    #
    cpi
    cdiv
    co
    @19
    @2
    @7
    @72
    cpi
    cdiv
    @2
    vs
    cA
    @6
    @71
    @2
    @26
    @5
    @28
    @30
    cdif
    #
    wcel
    #
    @6
    @71
    wceq
    wph
    @26
    @75
    @1
    wph
    cA
    @74
    @5
    fourierdlem95.ass
    sselda
    #
    adantlr
    wph
    @74
    cD
    cS
    cU
    vn
    cF
    cG
    cH
    cK
    cW
    cX
    cY
    vs
    fourierdlem95.f
    fourierdlem95.xre
    @39
    @42
    fourierdlem95.d
    fourierdlem95.h
    fourierdlem95.k
    fourierdlem95.u
    fourierdlem95.s
    fourierdlem95.g
    @74
    eqid
    fourierdlem66
    syldan
    #
    itgeq2dv
    oveq1d
    @2
    @72
    @73
    cpi
    cdiv
    @2
    @73
    @72
    @2
    vs
    cA
    @18
    cpi
    cr
    @2
    cpi
    @64
    recnd
    #
    @2
    @26
    wa
    #
    @17
    @10
    wph
    @26
    @17
    cr
    wcel
    @1
    wph
    @26
    wa
    #
    @14
    @16
    @80
    cr
    cr
    @13
    cF
    wph
    @32
    @26
    fourierdlem95.f
    adantr
    @80
    cX
    @5
    wph
    @34
    @26
    fourierdlem95.xre
    adantr
    @80
    @74
    cr
    @5
    @74
    @28
    cr
    @28
    @30
    difss
    @27
    cr
    wcel
    #
    @63
    @28
    cr
    wss
    #
    cpi
    pire
    renegcli
    #
    pire
    @27
    cpi
    iccssre
    mp2an
    #
    sstri
    @76
    sseldi
    #
    readdcld
    ffvelrnd
    #
    wph
    @16
    cr
    wcel
    @26
    wph
    @15
    cY
    cW
    cr
    @39
    @42
    ifcld
    adantr
    #
    resubcld
    adantlr
    @79
    @1
    @5
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @2
    @1
    @26
    @25
    adantr
    wph
    @26
    @88
    @1
    @85
    adantlr
    cD
    @5
    vn
    @0
    vs
    fourierdlem95.d
    dirkerre
    #
    syl2anc
    #
    remulcld
    #
    @2
    vs
    cA
    @18
    cmpt
    vs
    cA
    c1
    cpi
    cdiv
    co
    #
    @6
    cmul
    co
    #
    cmpt
    cibl
    @2
    vs
    cA
    @18
    @94
    @79
    @94
    cpi
    cpi
    cdiv
    co
    #
    @18
    cmul
    co
    #
    c1
    @18
    cmul
    co
    @18
    @79
    @71
    cpi
    cdiv
    co
    @6
    cpi
    cdiv
    co
    @96
    @94
    @79
    @71
    @6
    cpi
    cdiv
    @79
    @6
    @71
    @77
    eqcomd
    oveq1d
    @79
    cpi
    @18
    cpi
    cpi
    cc
    wcel
    @79
    picn
    a1i
    #
    @79
    @18
    @92
    recnd
    #
    @97
    @65
    @79
    @66
    a1i
    #
    div23d
    @79
    @6
    cpi
    @79
    @6
    @46
    recnd
    @97
    @99
    divrec2d
    3eqtr3rd
    @79
    @95
    c1
    @18
    cmul
    @95
    c1
    wceq
    @79
    cpi
    picn
    @66
    dividi
    a1i
    oveq1d
    @79
    @18
    @98
    mulid2d
    3eqtrrd
    mpteq2dva
    @2
    vs
    cA
    @6
    @93
    cr
    @2
    cpi
    @78
    @67
    reccld
    @46
    @62
    iblmulc2
    eqeltrd
    #
    itgmulc2
    eqcomd
    oveq1d
    @2
    @19
    cpi
    @2
    vs
    cA
    @18
    cr
    @92
    @100
    itgcl
    @78
    @67
    divcan3d
    3eqtrd
    @2
    vs
    cA
    @10
    cO
    cr
    wph
    cO
    cc
    wcel
    @1
    @70
    adantr
    #
    @91
    @2
    vs
    cA
    @28
    @10
    cr
    @31
    @47
    @1
    @29
    @89
    wph
    @29
    @1
    @88
    @89
    @28
    cr
    @5
    @84
    sseli
    @90
    sylan2
    #
    adantll
    @2
    @81
    @63
    vs
    @28
    @10
    cmpt
    #
    @28
    cc
    ccncf
    co
    #
    wcel
    #
    @103
    cibl
    wcel
    @81
    @2
    @83
    a1i
    @64
    @1
    @105
    wph
    @1
    @28
    cr
    ccncf
    co
    #
    @104
    @103
    @1
    cr
    cc
    wss
    #
    cc
    cc
    wss
    @106
    @104
    wss
    @107
    @1
    ax-resscn
    a1i
    cc
    ssid
    @28
    cr
    cc
    cncfss
    sylancl
    @1
    vs
    cr
    cr
    @28
    cr
    @10
    vs
    cr
    @10
    cmpt
    #
    @108
    eqid
    @1
    @9
    @108
    cr
    cr
    ccncf
    co
    @1
    vs
    cr
    cr
    @9
    vs
    cD
    vn
    @0
    fourierdlem95.d
    dirkerf
    feqmptd
    vs
    cD
    vn
    @0
    fourierdlem95.d
    dirkercncf
    eqeltrrd
    @82
    @1
    @84
    a1i
    cr
    cr
    wss
    @1
    cr
    ssid
    a1i
    @102
    cncfmptssg
    sseldd
    adantl
    @27
    cpi
    @103
    cniccibl
    syl3anc
    iblss
    #
    itgmulc2
    oveq12d
    @2
    vs
    cA
    @18
    @20
    caddc
    co
    #
    citg
    @22
    @24
    @2
    vs
    cA
    @18
    @20
    cr
    @92
    @100
    @79
    cO
    @10
    wph
    cO
    cr
    wcel
    @1
    @26
    fourierdlem95.o
    ad2antrr
    @91
    remulcld
    @2
    vs
    cA
    @10
    cO
    cr
    @101
    @91
    @109
    iblmulc2
    itgadd
    @2
    vs
    cA
    @110
    @23
    @79
    @110
    @18
    @16
    @10
    cmul
    co
    #
    caddc
    co
    @23
    @111
    cmin
    co
    #
    @111
    caddc
    co
    @23
    @79
    @20
    @111
    @18
    caddc
    @79
    cO
    @16
    @10
    cmul
    wph
    @26
    cO
    @16
    wceq
    @1
    @80
    @16
    cO
    fourierdlem95.ifeqo
    eqcomd
    adantlr
    oveq1d
    oveq2d
    @79
    @18
    @112
    @111
    caddc
    @79
    @14
    @16
    @10
    wph
    @26
    @14
    cc
    wcel
    @1
    @80
    @14
    @86
    recnd
    adantlr
    #
    wph
    @26
    @16
    cc
    wcel
    @1
    @80
    @16
    @87
    recnd
    adantlr
    #
    @79
    @10
    @91
    recnd
    #
    subdird
    oveq1d
    @79
    @23
    @111
    @79
    @14
    @10
    @113
    @115
    mulcld
    @79
    @16
    @10
    @114
    @115
    mulcld
    npcand
    3eqtrd
    itgeq2dv
    eqtr3d
    3eqtrd
end
