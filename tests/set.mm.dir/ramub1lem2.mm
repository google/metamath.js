include "cv.mm"
include "cfv.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "cpw.mm"
include "wrex.mm"
include "cfn.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "diffi.mm"
include "cram.mm"
include "nn0red.mm"
include "leidd.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "cun.mm"
include "caddc.mm"
include "undif1.mm"
include "wceq.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "wn.mm"
include "neldifsnd.mm"
include "wi.mm"
include "hashunsng.mm"
include "mp2and.mm"
include "3eqtr3d.mm"
include "addcan2ad.mm"
include "breqtrrd.mm"
include "wf.mm"
include "adantr.mm"
include "crab.mm"
include "hashbcval.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "simprbda.mm"
include "elpwid.mm"
include "difss2d.mm"
include "unssd.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ssfi.mm"
include "ssneldd.mm"
include "simplbda.mm"
include "oveq1d.mm"
include "cc.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "sylanbrc.mm"
include "nnnn0d.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "rami.mm"
include "cif.mm"
include "cmpt.mm"
include "cres.mm"
include "simprll.mm"
include "ffvelrnda.mm"
include "ifcld.mm"
include "eqid.mm"
include "equequ2.mm"
include "ifbieq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqeltrrd.mm"
include "simprlr.mm"
include "simprrl.mm"
include "eqbrtrrd.mm"
include "hashbcss.mm"
include "syl3anc.mm"
include "fssresd.mm"
include "equequ1.mm"
include "ifbieq2d.mm"
include "fvex.mm"
include "ifex.mm"
include "ad2antrl.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "ad2antrr.mm"
include "simprrr.mm"
include "cin.mm"
include "cnvresima.mm"
include "inss1.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "ramub1lem1.mm"
include "expr.mm"
include "sylbid.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimdvva.mm"

theorem ramub1lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cC: class C
  let cR: class R
  let cS: class S
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cD: class D
  let vd: setvar d
  let vf: setvar f
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let cW: class W
  let cV: class V
  let cE: class E
  assume ramub1.m: |- ( ph -> M e. NN )
  assume ramub1.r: |- ( ph -> R e. Fin )
  assume ramub1.f: |- ( ph -> F : R --> NN )
  assume ramub1.g: |- G = ( x e. R |-> ( M Ramsey ( y e. R |-> if ( y = x , ( ( F ` x ) - 1 ) , ( F ` y ) ) ) ) )
  assume ramub1.1: |- ( ph -> G : R --> NN0 )
  assume ramub1.2: |- ( ph -> ( ( M - 1 ) Ramsey G ) e. NN0 )
  assume ramub1.3: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume ramub1.4: |- ( ph -> S e. Fin )
  assume ramub1.5: |- ( ph -> ( # ` S ) = ( ( ( M - 1 ) Ramsey G ) + 1 ) )
  assume ramub1.6: |- ( ph -> K : ( S C M ) --> R )
  assume ramub1.x: |- ( ph -> X e. S )
  assume ramub1.h: |- H = ( u e. ( ( S \ { X } ) C ( M - 1 ) ) |-> ( K ` ( u u. { X } ) ) )

  disjoint u x
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a b
  disjoint a c
  disjoint a i
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint M a
  disjoint b c
  disjoint b i
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint G a
  disjoint G c
  disjoint G i
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint R c
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint c ph
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S c
  disjoint S i
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint C c
  disjoint C u
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H c
  disjoint H u
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K c
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint X a
  disjoint X c
  disjoint X i
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint D u
  disjoint D x
  disjoint c d
  disjoint c f
  disjoint c s
  disjoint c v
  disjoint c w
  disjoint d f
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint a d
  disjoint a f
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint b d
  disjoint b f
  disjoint b s
  disjoint b v
  disjoint b w
  disjoint d i
  disjoint M d
  disjoint f i
  disjoint M f
  disjoint i s
  disjoint i v
  disjoint i w
  disjoint M s
  disjoint M v
  disjoint M w
  disjoint G d
  disjoint G f
  disjoint G s
  disjoint G v
  disjoint G w
  disjoint R d
  disjoint R f
  disjoint R s
  disjoint R v
  disjoint R w
  disjoint W a
  disjoint W i
  disjoint W u
  disjoint d ph
  disjoint f ph
  disjoint ph s
  disjoint ph v
  disjoint ph w
  disjoint S d
  disjoint S v
  disjoint S w
  disjoint V a
  disjoint V i
  disjoint V x
  disjoint V z
  disjoint C d
  disjoint C v
  disjoint C w
  disjoint H d
  disjoint H v
  disjoint H w
  disjoint K d
  disjoint K v
  disjoint K w
  disjoint E x
  disjoint E z
  disjoint X d
  disjoint X v
  disjoint X w
  assert |- ( ph -> E. c e. R E. z e. ~P S ( ( F ` c ) <_ ( # ` z ) /\ ( z C M ) C_ ( `' K " { c } ) ) )

  proof
    wph
    vd
    cv
    #
    cG
    cfv
    #
    vw
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @2
    cM
    c1
    cmin
    co
    #
    cC
    co
    cH
    ccnv
    @0
    csn
    cima
    wss
    #
    wa
    #
    vw
    cS
    cX
    csn
    #
    cdif
    #
    cpw
    #
    wrex
    vd
    cR
    wrex
    vc
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    chash
    cfv
    cle
    wbr
    @13
    cM
    cC
    co
    cK
    ccnv
    @11
    csn
    #
    cima
    #
    wss
    wa
    vz
    cS
    cpw
    #
    wrex
    #
    vc
    cR
    wrex
    #
    wph
    vw
    cC
    cR
    @9
    vi
    cG
    cH
    @5
    cfn
    cfn
    va
    vb
    vd
    ramub1.3
    wph
    cM
    cn
    wcel
    #
    @5
    cn0
    wcel
    #
    ramub1.m
    cM
    nnm1nn0
    syl
    #
    ramub1.r
    ramub1.1
    ramub1.2
    wph
    cS
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    ramub1.4
    cS
    @8
    diffi
    syl
    #
    wph
    @5
    cG
    cram
    co
    #
    @25
    @9
    chash
    cfv
    #
    cle
    wph
    @25
    wph
    @25
    ramub1.2
    nn0red
    leidd
    wph
    @26
    @25
    c1
    wph
    @26
    wph
    @23
    @26
    cn0
    wcel
    @24
    @9
    hashcl
    syl
    nn0cnd
    wph
    @25
    ramub1.2
    nn0cnd
    wph
    1cnd
    wph
    @9
    @8
    cun
    #
    chash
    cfv
    #
    cS
    chash
    cfv
    #
    @26
    c1
    caddc
    co
    #
    @25
    c1
    caddc
    co
    #
    wph
    @27
    cS
    chash
    wph
    @27
    cS
    @8
    cun
    #
    cS
    cS
    @8
    undif1
    wph
    @8
    cS
    wss
    #
    @32
    cS
    wceq
    wph
    cX
    cS
    ramub1.x
    snssd
    #
    @8
    cS
    ssequn2
    sylib
    syl5eq
    fveq2d
    wph
    @23
    cX
    @9
    wcel
    wn
    #
    @28
    @30
    wceq
    #
    @24
    wph
    cX
    cS
    neldifsnd
    wph
    cX
    cS
    wcel
    #
    @23
    @35
    wa
    @36
    wi
    ramub1.x
    @9
    cX
    cS
    hashunsng
    syl
    mp2and
    ramub1.5
    3eqtr3d
    addcan2ad
    breqtrrd
    wph
    vu
    @9
    @5
    cC
    co
    #
    vu
    cv
    #
    @8
    cun
    #
    cK
    cfv
    cR
    cH
    wph
    @39
    @38
    wcel
    #
    wa
    #
    cS
    cM
    cC
    co
    #
    cR
    @40
    cK
    wph
    @43
    cR
    cK
    wf
    #
    @41
    ramub1.6
    adantr
    @42
    @40
    vx
    cv
    #
    chash
    cfv
    #
    cM
    wceq
    #
    vx
    @16
    crab
    #
    @43
    @42
    @40
    @16
    wcel
    #
    @40
    chash
    cfv
    #
    cM
    wceq
    #
    @40
    @48
    wcel
    @42
    @40
    cS
    wss
    @49
    @42
    @39
    @8
    cS
    @42
    @39
    cS
    @8
    @42
    @39
    @9
    wph
    @41
    @39
    @10
    wcel
    #
    @39
    chash
    cfv
    #
    @5
    wceq
    #
    wph
    @41
    @39
    @46
    @5
    wceq
    #
    vx
    @10
    crab
    #
    wcel
    @52
    @54
    wa
    wph
    @38
    @56
    @39
    wph
    @23
    @20
    @38
    @56
    wceq
    @24
    @21
    vx
    @9
    cC
    vi
    @5
    cfn
    va
    vb
    ramub1.3
    hashbcval
    syl2anc
    eleq2d
    @55
    @54
    vx
    @39
    @10
    vx
    vu
    weq
    @46
    @53
    @5
    @45
    @39
    chash
    fveq2
    eqeq1d
    elrab
    syl6bb
    #
    simprbda
    elpwid
    #
    difss2d
    wph
    @33
    @41
    @34
    adantr
    unssd
    @40
    cS
    @39
    @8
    vu
    vex
    cX
    snex
    unex
    elpw
    sylibr
    @42
    @50
    @53
    c1
    caddc
    co
    #
    @5
    c1
    caddc
    co
    #
    cM
    @42
    @39
    cfn
    wcel
    #
    cX
    @39
    wcel
    wn
    #
    @50
    @59
    wceq
    #
    @42
    @23
    @39
    @9
    wss
    @61
    wph
    @23
    @41
    @24
    adantr
    @58
    @9
    @39
    ssfi
    syl2anc
    @42
    @39
    @9
    cX
    @58
    @42
    cX
    cS
    neldifsnd
    ssneldd
    @42
    @37
    @61
    @62
    wa
    @63
    wi
    wph
    @37
    @41
    ramub1.x
    adantr
    @39
    cX
    cS
    hashunsng
    syl
    mp2and
    @42
    @53
    @5
    c1
    caddc
    wph
    @41
    @52
    @54
    @57
    simplbda
    oveq1d
    wph
    @60
    cM
    wceq
    #
    @41
    wph
    cM
    cc
    wcel
    c1
    cc
    wcel
    @64
    wph
    cM
    ramub1.m
    nncnd
    ax-1cn
    cM
    c1
    npcan
    sylancl
    adantr
    3eqtrd
    @47
    @51
    vx
    @40
    @16
    @45
    @40
    wceq
    @46
    @50
    cM
    @45
    @40
    chash
    fveq2
    eqeq1d
    elrab
    sylanbrc
    wph
    @43
    @48
    wceq
    #
    @41
    wph
    @22
    cM
    cn0
    wcel
    #
    @65
    ramub1.4
    wph
    cM
    ramub1.m
    nnnn0d
    #
    vx
    cS
    cC
    vi
    cM
    cfn
    va
    vb
    ramub1.3
    hashbcval
    syl2anc
    adantr
    eleqtrrd
    ffvelrnd
    ramub1.h
    fmptd
    rami
    wph
    @7
    @18
    vd
    vw
    cR
    @10
    wph
    @0
    cR
    wcel
    #
    @2
    @10
    wcel
    #
    wa
    #
    @7
    @18
    wph
    @70
    @7
    wa
    #
    wa
    #
    @11
    vy
    cR
    vy
    vd
    weq
    #
    @0
    cF
    cfv
    #
    c1
    cmin
    co
    #
    vy
    cv
    #
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    #
    vv
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @81
    cM
    cC
    co
    #
    cK
    @2
    cM
    cC
    co
    #
    cres
    #
    ccnv
    @14
    cima
    #
    wss
    #
    wa
    #
    vv
    @2
    cpw
    #
    wrex
    #
    vc
    cR
    wrex
    @18
    @72
    vv
    cC
    cR
    @2
    vi
    @79
    @86
    cM
    cfn
    @10
    va
    vb
    vc
    ramub1.3
    wph
    @66
    @71
    @67
    adantr
    #
    wph
    cR
    cfn
    wcel
    #
    @71
    ramub1.r
    adantr
    @72
    vy
    cR
    @78
    cn0
    @79
    @72
    @76
    cR
    wcel
    #
    wa
    #
    @73
    @75
    @77
    cn0
    @72
    @75
    cn0
    wcel
    #
    @94
    @72
    @74
    cn
    wcel
    @96
    @72
    cR
    cn
    @0
    cF
    wph
    cR
    cn
    cF
    wf
    #
    @71
    ramub1.f
    adantr
    #
    wph
    @68
    @69
    @7
    simprll
    #
    ffvelrnd
    @74
    nnm1nn0
    syl
    adantr
    @95
    @77
    @72
    cR
    cn
    @76
    cF
    @98
    ffvelrnda
    nnnn0d
    ifcld
    @79
    eqid
    #
    fmptd
    @72
    @1
    cM
    @79
    cram
    co
    #
    cn0
    @72
    @68
    @1
    @101
    wceq
    @99
    vx
    @0
    cM
    vy
    cR
    vy
    vx
    weq
    #
    @45
    cF
    cfv
    #
    c1
    cmin
    co
    #
    @77
    cif
    #
    cmpt
    #
    cram
    co
    @101
    cR
    cG
    vx
    vd
    weq
    #
    @106
    @79
    cM
    cram
    @107
    vy
    cR
    @105
    @78
    @107
    @102
    @73
    @104
    @75
    @77
    vx
    vd
    vy
    equequ2
    @107
    @103
    @74
    c1
    cmin
    @45
    @0
    cF
    fveq2
    oveq1d
    ifbieq1d
    mpteq2dv
    oveq2d
    ramub1.g
    cM
    @79
    cram
    ovex
    fvmpt
    syl
    #
    @72
    cR
    cn0
    @0
    cG
    wph
    cR
    cn0
    cG
    wf
    #
    @71
    ramub1.1
    adantr
    @99
    ffvelrnd
    eqeltrrd
    wph
    @68
    @69
    @7
    simprlr
    #
    @72
    @1
    @101
    @3
    cle
    @108
    wph
    @70
    @4
    @6
    simprrl
    #
    eqbrtrrd
    @72
    @43
    cR
    @85
    cK
    wph
    @44
    @71
    ramub1.6
    adantr
    @72
    @22
    @2
    cS
    wss
    @66
    @85
    @43
    wss
    wph
    @22
    @71
    ramub1.4
    adantr
    @72
    @2
    cS
    @8
    @72
    @2
    @9
    @110
    elpwid
    #
    difss2d
    @92
    cS
    @2
    cC
    vi
    cM
    cfn
    va
    vb
    ramub1.3
    hashbcss
    syl3anc
    fssresd
    rami
    @72
    @91
    @17
    vc
    cR
    @72
    @11
    cR
    wcel
    #
    wa
    @89
    @17
    vv
    @90
    @72
    @113
    @81
    @90
    wcel
    #
    @89
    @17
    wi
    @72
    @113
    @114
    wa
    #
    wa
    #
    @89
    vc
    vd
    weq
    #
    @75
    @12
    cif
    #
    @82
    cle
    wbr
    #
    @88
    wa
    #
    @17
    @116
    @83
    @119
    @88
    @116
    @80
    @118
    @82
    cle
    @113
    @80
    @118
    wceq
    @72
    @114
    vy
    @11
    @78
    @118
    cR
    @79
    vy
    vc
    weq
    @73
    @117
    @77
    @12
    @75
    vy
    vc
    vd
    equequ1
    @76
    @11
    cF
    fveq2
    ifbieq2d
    @100
    @117
    @75
    @12
    @74
    c1
    cmin
    ovex
    @11
    cF
    fvex
    ifex
    fvmpt
    ad2antrl
    breq1d
    anbi1d
    @72
    @115
    @120
    @17
    @72
    @115
    @120
    wa
    #
    wa
    #
    vx
    vy
    vz
    vu
    cC
    @0
    cR
    cS
    vi
    @11
    cF
    cG
    cH
    cK
    cM
    @81
    @2
    cX
    va
    vb
    wph
    @19
    @71
    @121
    ramub1.m
    ad2antrr
    wph
    @93
    @71
    @121
    ramub1.r
    ad2antrr
    wph
    @97
    @71
    @121
    ramub1.f
    ad2antrr
    ramub1.g
    wph
    @109
    @71
    @121
    ramub1.1
    ad2antrr
    wph
    @25
    cn0
    wcel
    @71
    @121
    ramub1.2
    ad2antrr
    ramub1.3
    wph
    @22
    @71
    @121
    ramub1.4
    ad2antrr
    wph
    @29
    @31
    wceq
    @71
    @121
    ramub1.5
    ad2antrr
    wph
    @44
    @71
    @121
    ramub1.6
    ad2antrr
    wph
    @37
    @71
    @121
    ramub1.x
    ad2antrr
    ramub1.h
    @72
    @68
    @121
    @99
    adantr
    @72
    @2
    @9
    wss
    @121
    @112
    adantr
    @72
    @4
    @121
    @111
    adantr
    @72
    @6
    @121
    wph
    @70
    @4
    @6
    simprrr
    adantr
    @72
    @113
    @114
    @120
    simprll
    @122
    @81
    @2
    @72
    @113
    @114
    @120
    simprlr
    elpwid
    @72
    @115
    @119
    @88
    simprrl
    @122
    @84
    @87
    @15
    @72
    @115
    @119
    @88
    simprrr
    @87
    @15
    @85
    cin
    @15
    @85
    @14
    cK
    cnvresima
    @15
    @85
    inss1
    eqsstri
    syl6ss
    ramub1lem1
    expr
    sylbid
    anassrs
    rexlimdva
    reximdva
    mpd
    expr
    rexlimdvva
    mpd
end
