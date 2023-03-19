include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "wceq.mm"
include "cun.mm"
include "wcel.mm"
include "cdif.mm"
include "sstrd.mm"
include "difss2d.mm"
include "snssd.mm"
include "unssd.mm"
include "cfn.mm"
include "wb.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbird.mm"
include "adantr.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cif.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqbrtrrd.mm"
include "cn.mm"
include "ffvelrnd.mm"
include "nnred.mm"
include "1red.mm"
include "cr.mm"
include "cn0.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashcl.mm"
include "nn0re.mm"
include "3syl.mm"
include "lesubaddd.mm"
include "mpbid.mm"
include "fveq2.mm"
include "wn.mm"
include "snidg.mm"
include "sseld.mm"
include "eldifn.mm"
include "syl6.mm"
include "mt2d.mm"
include "wi.mm"
include "hashunsng.mm"
include "mp2and.mm"
include "breqan12rd.mm"
include "crab.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "nnnn0d.mm"
include "hashbcval.mm"
include "w3a.mm"
include "simpl1l.mm"
include "eqsstr3d.mm"
include "simpr.mm"
include "simpl3.mm"
include "rabid.mm"
include "sylanbrc.mm"
include "sseldd.mm"
include "simpl2.mm"
include "elpwid.mm"
include "vex.mm"
include "elpw.mm"
include "sylibr.mm"
include "eleqtrrd.mm"
include "nnm1nn0.mm"
include "uncom.mm"
include "syl6sseq.mm"
include "ssundif.mm"
include "sylib.mm"
include "cvv.mm"
include "difexg.mm"
include "ax-mp.mm"
include "cc.mm"
include "diffi.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "neldifsnd.mm"
include "undif1.mm"
include "eldifd.mm"
include "elpwunsn.mm"
include "ssequn2.mm"
include "syl5req.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "mptiniseg.mm"
include "eleqtrd.mm"
include "uneq1.mm"
include "simprbi.mm"
include "simpl1r.mm"
include "3eqtr4d.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "pm2.61dan.mm"
include "rabssdv.mm"
include "eqsstrd.mm"
include "breq2d.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wne.mm"
include "ifnefalse.mm"
include "pm2.61dane.mm"

theorem ramub1lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
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
  assume ramub1.d: |- ( ph -> D e. R )
  assume ramub1.w: |- ( ph -> W C_ ( S \ { X } ) )
  assume ramub1.7: |- ( ph -> ( G ` D ) <_ ( # ` W ) )
  assume ramub1.8: |- ( ph -> ( W C ( M - 1 ) ) C_ ( `' H " { D } ) )
  assume ramub1.e: |- ( ph -> E e. R )
  assume ramub1.v: |- ( ph -> V C_ W )
  assume ramub1.9: |- ( ph -> if ( E = D , ( ( F ` D ) - 1 ) , ( F ` E ) ) <_ ( # ` V ) )
  assume ramub1.s: |- ( ph -> ( V C M ) C_ ( `' K " { E } ) )

  disjoint u x
  disjoint D u
  disjoint D x
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
  disjoint a i
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint M a
  disjoint b i
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint M b
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
  disjoint G i
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint W a
  disjoint W i
  disjoint W u
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S i
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V a
  disjoint V i
  disjoint V x
  disjoint V z
  disjoint C u
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H u
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint E x
  disjoint E z
  disjoint X a
  disjoint X i
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint c d
  disjoint c f
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
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
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b s
  disjoint b v
  disjoint b w
  disjoint c i
  disjoint M c
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
  disjoint G c
  disjoint G d
  disjoint G f
  disjoint G s
  disjoint G v
  disjoint G w
  disjoint R c
  disjoint R d
  disjoint R f
  disjoint R s
  disjoint R v
  disjoint R w
  disjoint c ph
  disjoint d ph
  disjoint f ph
  disjoint ph s
  disjoint ph v
  disjoint ph w
  disjoint S c
  disjoint S d
  disjoint S v
  disjoint S w
  disjoint C c
  disjoint C d
  disjoint C v
  disjoint C w
  disjoint H c
  disjoint H d
  disjoint H v
  disjoint H w
  disjoint K c
  disjoint K d
  disjoint K v
  disjoint K w
  disjoint X c
  disjoint X d
  disjoint X v
  disjoint X w
  assert |- ( ph -> E. z e. ~P S ( ( F ` E ) <_ ( # ` z ) /\ ( z C M ) C_ ( `' K " { E } ) ) )

  proof
    wph
    cE
    cF
    cfv
    #
    vz
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @1
    cM
    cC
    co
    #
    cK
    ccnv
    cE
    csn
    cima
    #
    wss
    #
    wa
    #
    vz
    cS
    cpw
    #
    wrex
    #
    cE
    cD
    wph
    cE
    cD
    wceq
    #
    wa
    #
    cV
    cX
    csn
    #
    cun
    #
    @8
    wcel
    #
    @0
    @13
    chash
    cfv
    #
    cle
    wbr
    #
    @13
    cM
    cC
    co
    #
    @5
    wss
    #
    @9
    wph
    @14
    @10
    wph
    @14
    @13
    cS
    wss
    #
    wph
    cV
    @12
    cS
    wph
    cV
    cS
    @12
    wph
    cV
    cW
    cS
    @12
    cdif
    #
    ramub1.v
    ramub1.w
    sstrd
    #
    difss2d
    #
    wph
    cX
    cS
    ramub1.x
    snssd
    unssd
    #
    wph
    cS
    cfn
    wcel
    #
    @14
    @19
    wb
    ramub1.4
    @13
    cS
    cfn
    elpw2g
    syl
    mpbird
    adantr
    @11
    @16
    cD
    cF
    cfv
    #
    cV
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @11
    @25
    c1
    cmin
    co
    #
    @26
    cle
    wbr
    @28
    @11
    @10
    @29
    @0
    cif
    #
    @29
    @26
    cle
    @10
    @30
    @29
    wceq
    wph
    @10
    @29
    @0
    iftrue
    adantl
    wph
    @30
    @26
    cle
    wbr
    #
    @10
    ramub1.9
    adantr
    eqbrtrrd
    @11
    @25
    c1
    @26
    @11
    @25
    wph
    @25
    cn
    wcel
    @10
    wph
    cR
    cn
    cD
    cF
    ramub1.f
    ramub1.d
    ffvelrnd
    adantr
    nnred
    @11
    1red
    wph
    @26
    cr
    wcel
    #
    @10
    wph
    cV
    cfn
    wcel
    #
    @26
    cn0
    wcel
    @32
    wph
    @24
    cV
    cS
    wss
    #
    @33
    ramub1.4
    @22
    cS
    cV
    ssfi
    syl2anc
    #
    cV
    hashcl
    @26
    nn0re
    3syl
    adantr
    lesubaddd
    mpbid
    @10
    wph
    @0
    @25
    @15
    @27
    cle
    cE
    cD
    cF
    fveq2
    wph
    @33
    cX
    cV
    wcel
    #
    wn
    #
    @15
    @27
    wceq
    #
    @35
    wph
    @36
    cX
    @12
    wcel
    #
    wph
    cX
    cS
    wcel
    #
    @39
    ramub1.x
    cX
    cS
    snidg
    syl
    wph
    @36
    cX
    @20
    wcel
    @39
    wn
    wph
    cV
    @20
    cX
    @21
    sseld
    cX
    cS
    @12
    eldifn
    syl6
    mt2d
    wph
    @40
    @33
    @37
    wa
    @38
    wi
    ramub1.x
    cV
    cX
    cS
    hashunsng
    syl
    mp2and
    breqan12rd
    mpbird
    @11
    @17
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
    @13
    cpw
    #
    crab
    #
    @5
    wph
    @17
    @45
    wceq
    #
    @10
    wph
    @13
    cfn
    wcel
    #
    cM
    cn0
    wcel
    #
    @46
    wph
    @33
    @12
    cfn
    wcel
    @47
    @35
    cX
    snfi
    cV
    @12
    unfi
    sylancl
    wph
    cM
    ramub1.m
    nnnn0d
    #
    vx
    @13
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
    @11
    @43
    vx
    @44
    @5
    @11
    @41
    @44
    wcel
    #
    @43
    w3a
    #
    @41
    cV
    cpw
    #
    wcel
    #
    @41
    @5
    wcel
    #
    @51
    @53
    wa
    #
    @43
    vx
    @52
    crab
    #
    @5
    @41
    @55
    wph
    @56
    @5
    wss
    wph
    @10
    @50
    @43
    @53
    simpl1l
    wph
    @56
    cV
    cM
    cC
    co
    #
    @5
    wph
    @33
    @48
    @57
    @56
    wceq
    @35
    @49
    vx
    cV
    cC
    vi
    cM
    cfn
    va
    vb
    ramub1.3
    hashbcval
    syl2anc
    ramub1.s
    eqsstr3d
    syl
    @55
    @53
    @43
    @41
    @56
    wcel
    @51
    @53
    simpr
    @11
    @50
    @43
    @53
    simpl3
    @43
    vx
    @52
    rabid
    sylanbrc
    sseldd
    @51
    @53
    wn
    #
    wa
    #
    @54
    @41
    cS
    cM
    cC
    co
    #
    wcel
    #
    @41
    cK
    cfv
    #
    cE
    wceq
    #
    @59
    @41
    @43
    vx
    @8
    crab
    #
    @60
    @59
    @41
    @8
    wcel
    #
    @43
    @41
    @64
    wcel
    @59
    @41
    cS
    wss
    #
    @65
    @59
    @41
    @13
    cS
    @59
    @41
    @13
    @11
    @50
    @43
    @58
    simpl2
    #
    elpwid
    #
    @59
    wph
    @19
    wph
    @10
    @50
    @43
    @58
    simpl1l
    #
    @23
    syl
    sstrd
    #
    @41
    cS
    vx
    vex
    #
    elpw
    sylibr
    @11
    @50
    @43
    @58
    simpl3
    #
    @43
    vx
    @8
    rabid
    sylanbrc
    @59
    wph
    @60
    @64
    wceq
    #
    @69
    wph
    @24
    @48
    @73
    ramub1.4
    @49
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
    syl
    eleqtrrd
    @59
    @41
    @12
    cdif
    #
    @12
    cun
    #
    cK
    cfv
    #
    cD
    @62
    cE
    @59
    @74
    vu
    cv
    #
    @12
    cun
    #
    cK
    cfv
    #
    cD
    wceq
    #
    vu
    @20
    cM
    c1
    cmin
    co
    #
    cC
    co
    #
    crab
    #
    wcel
    #
    @76
    cD
    wceq
    #
    @59
    @74
    cH
    ccnv
    cD
    csn
    cima
    #
    @83
    @59
    @77
    chash
    cfv
    #
    @81
    wceq
    #
    vu
    cW
    cpw
    #
    crab
    #
    @86
    @74
    @59
    wph
    @90
    @86
    wss
    @69
    wph
    @90
    cW
    @81
    cC
    co
    #
    @86
    wph
    cW
    cfn
    wcel
    #
    @81
    cn0
    wcel
    #
    @91
    @90
    wceq
    wph
    @24
    cW
    cS
    wss
    @92
    ramub1.4
    wph
    cW
    cS
    @12
    ramub1.w
    difss2d
    cS
    cW
    ssfi
    syl2anc
    wph
    cM
    cn
    wcel
    @93
    ramub1.m
    cM
    nnm1nn0
    syl
    vu
    cW
    cC
    vi
    @81
    cfn
    va
    vb
    ramub1.3
    hashbcval
    syl2anc
    ramub1.8
    eqsstr3d
    syl
    @59
    @74
    @89
    wcel
    #
    @74
    chash
    cfv
    #
    @81
    wceq
    #
    @74
    @90
    wcel
    @59
    @74
    cW
    wss
    @94
    @59
    @74
    cV
    cW
    @59
    @41
    @12
    cV
    cun
    #
    wss
    @74
    cV
    wss
    @59
    @41
    @13
    @97
    @68
    cV
    @12
    uncom
    syl6sseq
    @41
    @12
    cV
    ssundif
    sylib
    @59
    wph
    cV
    cW
    wss
    @69
    ramub1.v
    syl
    sstrd
    @74
    cW
    @41
    cvv
    wcel
    @74
    cvv
    wcel
    @71
    @41
    @12
    cvv
    difexg
    ax-mp
    elpw
    sylibr
    @59
    @95
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @95
    @81
    @59
    @95
    cc
    wcel
    #
    c1
    cc
    wcel
    @99
    @95
    wceq
    @59
    @74
    cfn
    wcel
    #
    @95
    cn0
    wcel
    @100
    @59
    @41
    cfn
    wcel
    #
    @101
    @59
    @24
    @66
    @102
    @59
    wph
    @24
    @69
    ramub1.4
    syl
    @70
    cS
    @41
    ssfi
    syl2anc
    @41
    @12
    diffi
    syl
    #
    @74
    hashcl
    @95
    nn0cn
    3syl
    ax-1cn
    @95
    c1
    pncan
    sylancl
    @59
    @98
    cM
    c1
    cmin
    @59
    @75
    chash
    cfv
    #
    @98
    cM
    @59
    @101
    cX
    @74
    wcel
    wn
    #
    @104
    @98
    wceq
    #
    @103
    @59
    cX
    @41
    neldifsnd
    @59
    wph
    @40
    @101
    @105
    wa
    @106
    wi
    @69
    ramub1.x
    @74
    cX
    cS
    hashunsng
    3syl
    mp2and
    @59
    @42
    @104
    cM
    @59
    @41
    @75
    chash
    @59
    @75
    @41
    @12
    cun
    #
    @41
    @41
    @12
    undif1
    @59
    @12
    @41
    wss
    @107
    @41
    wceq
    @59
    cX
    @41
    @59
    @41
    @44
    @52
    cdif
    wcel
    cX
    @41
    wcel
    @59
    @41
    @44
    @52
    @67
    @51
    @58
    simpr
    eldifd
    @41
    cV
    cX
    elpwunsn
    syl
    snssd
    @12
    @41
    ssequn2
    sylib
    syl5req
    #
    fveq2d
    @72
    eqtr3d
    eqtr3d
    oveq1d
    eqtr3d
    @88
    @96
    vu
    @74
    @89
    @77
    @74
    wceq
    #
    @87
    @95
    @81
    @77
    @74
    chash
    fveq2
    eqeq1d
    elrab
    sylanbrc
    sseldd
    @59
    wph
    cD
    cR
    wcel
    @86
    @83
    wceq
    @69
    ramub1.d
    vu
    @82
    @79
    cD
    cH
    cR
    ramub1.h
    mptiniseg
    3syl
    eleqtrd
    @84
    @74
    @82
    wcel
    @85
    @80
    @85
    vu
    @74
    @82
    @109
    @79
    @76
    cD
    @109
    @78
    @75
    cK
    @77
    @74
    @12
    uneq1
    fveq2d
    eqeq1d
    elrab
    simprbi
    syl
    @59
    @41
    @75
    cK
    @108
    fveq2d
    wph
    @10
    @50
    @43
    @58
    simpl1r
    3eqtr4d
    @59
    wph
    cK
    @60
    wfn
    #
    @54
    @61
    @63
    wa
    wb
    @69
    wph
    @60
    cR
    cK
    wf
    @110
    ramub1.6
    @60
    cR
    cK
    ffn
    syl
    @60
    cE
    @41
    cK
    fniniseg
    3syl
    mpbir2and
    pm2.61dan
    rabssdv
    eqsstrd
    @7
    @16
    @18
    wa
    vz
    @13
    @8
    @1
    @13
    wceq
    #
    @3
    @16
    @6
    @18
    @111
    @2
    @15
    @0
    cle
    @1
    @13
    chash
    fveq2
    breq2d
    @111
    @4
    @17
    @5
    @1
    @13
    cM
    cC
    oveq1
    sseq1d
    anbi12d
    rspcev
    syl12anc
    wph
    cE
    cD
    wne
    #
    wa
    #
    cV
    @8
    wcel
    #
    @0
    @26
    cle
    wbr
    #
    @57
    @5
    wss
    #
    @9
    wph
    @114
    @112
    wph
    @114
    @34
    @22
    wph
    @24
    @114
    @34
    wb
    ramub1.4
    cV
    cS
    cfn
    elpw2g
    syl
    mpbird
    adantr
    @113
    @30
    @0
    @26
    cle
    @112
    @30
    @0
    wceq
    wph
    cE
    cD
    @29
    @0
    ifnefalse
    adantl
    wph
    @31
    @112
    ramub1.9
    adantr
    eqbrtrrd
    wph
    @116
    @112
    ramub1.s
    adantr
    @7
    @115
    @116
    wa
    vz
    cV
    @8
    @1
    cV
    wceq
    #
    @3
    @115
    @6
    @116
    @117
    @2
    @26
    @0
    cle
    @1
    cV
    chash
    fveq2
    breq2d
    @117
    @4
    @57
    @5
    @1
    cV
    cM
    cC
    oveq1
    sseq1d
    anbi12d
    rspcev
    syl12anc
    pm2.61dane
end
