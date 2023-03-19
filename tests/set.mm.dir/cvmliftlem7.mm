include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "cc0.mm"
include "cdiv.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wa.mm"
include "caddc.mm"
include "fzssp1.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "syl5sseq.mm"
include "simpr.mm"
include "cz.mm"
include "wb.mm"
include "elfzelz.mm"
include "nnzd.mm"
include "elfzm1b.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "sseldd.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "cv.mm"
include "wi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cop.mm"
include "cvmliftlem4.mm"
include "a1i.mm"
include "nnne0d.mm"
include "div0d.mm"
include "0nn0.mm"
include "fvsng.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "wfn.mm"
include "ccn.mm"
include "wf.mm"
include "ccvm.mm"
include "cvmcn.mm"
include "syl.mm"
include "cnf.mm"
include "ffn.mm"
include "3syl.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "a1d.mm"
include "cuz.mm"
include "id.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "peano2fzr.mm"
include "ex.mm"
include "imim1d.mm"
include "cicc.mm"
include "ccom.mm"
include "cres.mm"
include "eqid.mm"
include "cle.mm"
include "wbr.mm"
include "simprlr.mm"
include "elfzle2.mm"
include "cn.mm"
include "simprll.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simprr.mm"
include "nn0cnd.mm"
include "pncan.mm"
include "oveq1d.mm"
include "3eltr4d.mm"
include "cvmliftlem6.mm"
include "simpld.mm"
include "cxr.mm"
include "nn0red.mm"
include "nndivred.mm"
include "rexrd.mm"
include "cr.mm"
include "peano2re.mm"
include "clt.mm"
include "ltp1d.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "ltled.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "simprd.mm"
include "reseq2d.mm"
include "fveq1d.mm"
include "feq2d.mm"
include "fvco3.mm"
include "fvres.mm"
include "3eqtr3d.mm"
include "expr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "nn0ind.mm"
include "impd.mm"
include "mpcom.mm"
include "syldan.mm"

theorem cvmliftlem7
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  let vy: setvar y
  let va: setvar a
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let cK: class K
  let wps: wff ps
  assume cvmliftlem.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmliftlem.b: |- B = U. C
  assume cvmliftlem.x: |- X = U. J
  assume cvmliftlem.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftlem.g: |- ( ph -> G e. ( II Cn J ) )
  assume cvmliftlem.p: |- ( ph -> P e. B )
  assume cvmliftlem.e: |- ( ph -> ( F ` P ) = ( G ` 0 ) )
  assume cvmliftlem.n: |- ( ph -> N e. NN )
  assume cvmliftlem.t: |- ( ph -> T : ( 1 ... N ) --> U_ j e. J ( { j } X. ( S ` j ) ) )
  assume cvmliftlem.a: |- ( ph -> A. k e. ( 1 ... N ) ( G " ( ( ( k - 1 ) / N ) [,] ( k / N ) ) ) C_ ( 1st ` ( T ` k ) ) )
  assume cvmliftlem.l: |- L = ( topGen ` ran (,) )
  assume cvmliftlem.q: |- Q = seq 0 ( ( x e. _V , m e. NN |-> ( z e. ( ( ( m - 1 ) / N ) [,] ( m / N ) ) |-> ( `' ( F |` ( iota_ b e. ( 2nd ` ( T ` m ) ) ( x ` ( ( m - 1 ) / N ) ) e. b ) ) ` ( G ` z ) ) ) ) , ( ( _I |` NN ) u. { <. 0 , { <. 0 , P >. } >. } ) )
  assume cvmliftlem5.3: |- W = ( ( ( M - 1 ) / N ) [,] ( M / N ) )

  disjoint b v
  disjoint b z
  disjoint B b
  disjoint v z
  disjoint B v
  disjoint B z
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b s
  disjoint b u
  disjoint b x
  disjoint F b
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint F v
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint L z
  disjoint M b
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint M x
  disjoint M z
  disjoint P b
  disjoint P k
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P z
  disjoint C b
  disjoint C j
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint C z
  disjoint j ph
  disjoint ph s
  disjoint ph x
  disjoint ph z
  disjoint N b
  disjoint N k
  disjoint N m
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N z
  disjoint S b
  disjoint S j
  disjoint S k
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S z
  disjoint X j
  disjoint G b
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G z
  disjoint T b
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint T z
  disjoint J b
  disjoint J j
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J z
  disjoint Q b
  disjoint Q k
  disjoint Q m
  disjoint Q u
  disjoint Q v
  disjoint Q x
  disjoint Q z
  disjoint W k
  disjoint W m
  disjoint W x
  disjoint W z
  disjoint b y
  disjoint v y
  disjoint y z
  disjoint B y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint j y
  disjoint k n
  disjoint k t
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m y
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s t
  disjoint s w
  disjoint s y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u w
  disjoint u y
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint F y
  disjoint L n
  disjoint L y
  disjoint K f
  disjoint K y
  disjoint M a
  disjoint M c
  disjoint M y
  disjoint P f
  disjoint P g
  disjoint P n
  disjoint C a
  disjoint C c
  disjoint C f
  disjoint C g
  disjoint C n
  disjoint C y
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint n ph
  disjoint ph y
  disjoint ps z
  disjoint N c
  disjoint N n
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S g
  disjoint S n
  disjoint X a
  disjoint G a
  disjoint G f
  disjoint G g
  disjoint G n
  disjoint G t
  disjoint G w
  disjoint G y
  disjoint T a
  disjoint T c
  disjoint T y
  disjoint J a
  disjoint J c
  disjoint J f
  disjoint J g
  disjoint J n
  disjoint Q c
  disjoint Q n
  disjoint Q y
  assert |- ( ( ph /\ M e. ( 1 ... N ) ) -> ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) e. ( `' F " { ( G ` ( ( M - 1 ) / N ) ) } ) )

  proof
    wph
    cM
    c1
    cN
    cfz
    co
    #
    wcel
    #
    cM
    c1
    cmin
    co
    #
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    @2
    cN
    cdiv
    co
    #
    @2
    cQ
    cfv
    #
    cfv
    #
    cF
    ccnv
    #
    @5
    cG
    cfv
    #
    csn
    #
    cima
    #
    wcel
    #
    wph
    @1
    wa
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @3
    @2
    @13
    cc0
    @14
    c1
    caddc
    co
    #
    cfz
    co
    @15
    @3
    cc0
    @14
    fzssp1
    @13
    @16
    cN
    cc0
    cfz
    @13
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @16
    cN
    wceq
    wph
    @17
    @1
    wph
    cN
    cvmliftlem.n
    nncnd
    #
    adantr
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq2d
    syl5sseq
    @13
    @1
    @2
    @15
    wcel
    #
    wph
    @1
    simpr
    @1
    cM
    cz
    wcel
    cN
    cz
    wcel
    #
    @1
    @20
    wb
    wph
    cM
    c1
    cN
    elfzelz
    wph
    cN
    cvmliftlem.n
    nnzd
    #
    cM
    cN
    elfzm1b
    syl2anr
    mpbid
    sseldd
    @2
    cn0
    wcel
    #
    wph
    @4
    wa
    @12
    @4
    @23
    wph
    @2
    cN
    elfznn0
    adantl
    @23
    wph
    @4
    @12
    wph
    vy
    cv
    #
    @3
    wcel
    #
    @24
    cN
    cdiv
    co
    #
    @24
    cQ
    cfv
    #
    cfv
    #
    @8
    @26
    cG
    cfv
    #
    csn
    #
    cima
    #
    wcel
    #
    wi
    #
    wi
    wph
    cc0
    @3
    wcel
    #
    cc0
    cN
    cdiv
    co
    #
    cc0
    cQ
    cfv
    #
    cfv
    #
    @8
    @35
    cG
    cfv
    #
    csn
    #
    cima
    #
    wcel
    #
    wi
    #
    wi
    wph
    vn
    cv
    #
    @3
    wcel
    #
    @43
    cN
    cdiv
    co
    #
    @43
    cQ
    cfv
    #
    cfv
    #
    @8
    @45
    cG
    cfv
    #
    csn
    #
    cima
    #
    wcel
    #
    wi
    #
    wi
    wph
    @43
    c1
    caddc
    co
    #
    @3
    wcel
    #
    @53
    cN
    cdiv
    co
    #
    @53
    cQ
    cfv
    #
    cfv
    #
    @8
    @55
    cG
    cfv
    #
    csn
    #
    cima
    #
    wcel
    #
    wi
    #
    wi
    wph
    @4
    @12
    wi
    #
    wi
    vy
    vn
    @2
    @24
    cc0
    wceq
    #
    @33
    @42
    wph
    @64
    @25
    @34
    @32
    @41
    @24
    cc0
    @3
    eleq1
    @64
    @28
    @37
    @31
    @40
    @64
    @26
    @35
    @27
    @36
    @24
    cc0
    cQ
    fveq2
    @24
    cc0
    cN
    cdiv
    oveq1
    #
    fveq12d
    @64
    @30
    @39
    @8
    @64
    @29
    @38
    @64
    @26
    @35
    cG
    @65
    fveq2d
    sneqd
    imaeq2d
    eleq12d
    imbi12d
    imbi2d
    @24
    @43
    wceq
    #
    @33
    @52
    wph
    @66
    @25
    @44
    @32
    @51
    @24
    @43
    @3
    eleq1
    @66
    @28
    @47
    @31
    @50
    @66
    @26
    @45
    @27
    @46
    @24
    @43
    cQ
    fveq2
    @24
    @43
    cN
    cdiv
    oveq1
    #
    fveq12d
    @66
    @30
    @49
    @8
    @66
    @29
    @48
    @66
    @26
    @45
    cG
    @67
    fveq2d
    sneqd
    imaeq2d
    eleq12d
    imbi12d
    imbi2d
    @24
    @53
    wceq
    #
    @33
    @62
    wph
    @68
    @25
    @54
    @32
    @61
    @24
    @53
    @3
    eleq1
    @68
    @28
    @57
    @31
    @60
    @68
    @26
    @55
    @27
    @56
    @24
    @53
    cQ
    fveq2
    @24
    @53
    cN
    cdiv
    oveq1
    #
    fveq12d
    @68
    @30
    @59
    @8
    @68
    @29
    @58
    @68
    @26
    @55
    cG
    @69
    fveq2d
    sneqd
    imaeq2d
    eleq12d
    imbi12d
    imbi2d
    @24
    @2
    wceq
    #
    @33
    @63
    wph
    @70
    @25
    @4
    @32
    @12
    @24
    @2
    @3
    eleq1
    @70
    @28
    @7
    @31
    @11
    @70
    @26
    @5
    @27
    @6
    @24
    @2
    cQ
    fveq2
    @24
    @2
    cN
    cdiv
    oveq1
    #
    fveq12d
    @70
    @30
    @10
    @8
    @70
    @29
    @9
    @70
    @26
    @5
    cG
    @71
    fveq2d
    sneqd
    imaeq2d
    eleq12d
    imbi12d
    imbi2d
    wph
    @41
    @34
    wph
    @37
    cP
    @40
    wph
    @37
    cc0
    cc0
    cP
    cop
    csn
    #
    cfv
    #
    cP
    wph
    @35
    cc0
    @36
    @72
    @36
    @72
    wceq
    wph
    wph
    vx
    vz
    vv
    vu
    cB
    cC
    cP
    cQ
    cS
    cT
    vj
    vk
    vm
    cF
    cG
    cJ
    cL
    cN
    cX
    vs
    vb
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    cvmliftlem.q
    cvmliftlem4
    a1i
    wph
    cN
    @19
    wph
    cN
    cvmliftlem.n
    nnne0d
    div0d
    #
    fveq12d
    wph
    cc0
    cn0
    wcel
    cP
    cB
    wcel
    #
    @73
    cP
    wceq
    0nn0
    cvmliftlem.p
    cc0
    cP
    cn0
    cB
    fvsng
    sylancr
    eqtrd
    wph
    cP
    @40
    wcel
    #
    @75
    cP
    cF
    cfv
    #
    @38
    wceq
    #
    cvmliftlem.p
    wph
    @77
    cc0
    cG
    cfv
    @38
    cvmliftlem.e
    wph
    @35
    cc0
    cG
    @74
    fveq2d
    eqtr4d
    wph
    cF
    cB
    wfn
    #
    @76
    @75
    @78
    wa
    wb
    wph
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    cB
    cX
    cF
    wf
    @79
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    @80
    cvmliftlem.f
    cC
    cF
    cJ
    cvmcn
    syl
    cF
    cC
    cJ
    cB
    cX
    cvmliftlem.b
    cvmliftlem.x
    cnf
    cB
    cX
    cF
    ffn
    3syl
    #
    cB
    @38
    cP
    cF
    fniniseg
    syl
    mpbir2and
    eqeltrd
    a1d
    @43
    cn0
    wcel
    #
    wph
    @52
    @62
    wph
    @82
    @52
    @62
    wi
    wph
    @82
    wa
    #
    @52
    @54
    @51
    wi
    @62
    @83
    @54
    @44
    @51
    @83
    @43
    cc0
    cuz
    cfv
    #
    wcel
    #
    @54
    @44
    wi
    @82
    @85
    wph
    @82
    @43
    cn0
    @84
    @82
    id
    nn0uz
    syl6eleq
    adantl
    @85
    @54
    @44
    @43
    cc0
    cN
    peano2fzr
    ex
    syl
    imim1d
    @83
    @54
    @51
    @61
    wph
    @82
    @54
    @51
    @61
    wi
    wph
    @82
    @54
    wa
    #
    @51
    @61
    wph
    @86
    @51
    wa
    #
    wa
    #
    @61
    @57
    cB
    wcel
    #
    @57
    cF
    cfv
    #
    @58
    wceq
    #
    @88
    @53
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    @55
    cicc
    co
    #
    cB
    @55
    @56
    @88
    @94
    cB
    @56
    wf
    #
    cF
    @56
    ccom
    #
    cG
    @94
    cres
    #
    wceq
    #
    wph
    @87
    vx
    vz
    vv
    vu
    cB
    cC
    cP
    cQ
    cS
    cT
    vj
    vk
    vm
    cF
    cG
    cJ
    cL
    @53
    cN
    @94
    cX
    vs
    vb
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    cvmliftlem.q
    @94
    eqid
    @88
    @53
    @0
    wcel
    #
    @53
    cN
    cle
    wbr
    #
    @88
    @54
    @100
    wph
    @82
    @54
    @51
    simprlr
    @53
    cc0
    cN
    elfzle2
    syl
    @88
    @53
    c1
    cuz
    cfv
    #
    wcel
    @21
    @99
    @100
    wb
    @88
    @53
    cn
    @101
    @88
    @82
    @53
    cn
    wcel
    wph
    @82
    @54
    @51
    simprll
    #
    @43
    nn0p1nn
    syl
    nnuz
    syl6eleq
    wph
    @21
    @87
    @22
    adantr
    @53
    c1
    cN
    elfz5
    syl2anc
    mpbird
    @88
    @47
    @50
    @93
    @92
    cQ
    cfv
    #
    cfv
    @8
    @93
    cG
    cfv
    #
    csn
    #
    cima
    wph
    @86
    @51
    simprr
    @88
    @93
    @45
    @103
    @46
    @88
    @92
    @43
    cQ
    @88
    @43
    cc
    wcel
    @18
    @92
    @43
    wceq
    @88
    @43
    @102
    nn0cnd
    ax-1cn
    @43
    c1
    pncan
    sylancl
    #
    fveq2d
    @88
    @92
    @43
    cN
    cdiv
    @106
    oveq1d
    #
    fveq12d
    @88
    @105
    @49
    @8
    @88
    @104
    @48
    @88
    @93
    @45
    cG
    @107
    fveq2d
    sneqd
    imaeq2d
    3eltr4d
    cvmliftlem6
    #
    simpld
    #
    @88
    @55
    @45
    @55
    cicc
    co
    #
    @94
    @88
    @45
    cxr
    wcel
    @55
    cxr
    wcel
    @45
    @55
    cle
    wbr
    @55
    @110
    wcel
    #
    @88
    @45
    @88
    @43
    cN
    @88
    @43
    @102
    nn0red
    #
    wph
    cN
    cn
    wcel
    @87
    cvmliftlem.n
    adantr
    #
    nndivred
    #
    rexrd
    @88
    @55
    @88
    @53
    cN
    @88
    @43
    cr
    wcel
    #
    @53
    cr
    wcel
    #
    @112
    @43
    peano2re
    syl
    #
    @113
    nndivred
    #
    rexrd
    @88
    @45
    @55
    @114
    @118
    @88
    @43
    @53
    clt
    wbr
    #
    @45
    @55
    clt
    wbr
    #
    @88
    @43
    @112
    ltp1d
    @88
    @115
    @116
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @119
    @120
    wb
    @112
    @117
    @88
    cN
    @113
    nnred
    @88
    cN
    @113
    nngt0d
    @43
    @53
    cN
    ltdiv1
    syl112anc
    mpbid
    ltled
    @45
    @55
    ubicc2
    syl3anc
    #
    @88
    @93
    @45
    @55
    cicc
    @107
    oveq1d
    #
    eleqtrrd
    ffvelrnd
    @88
    @55
    @96
    cfv
    #
    @55
    cG
    @110
    cres
    #
    cfv
    #
    @90
    @58
    @88
    @55
    @96
    @124
    @88
    @96
    @97
    @124
    @88
    @95
    @98
    @108
    simprd
    @88
    @94
    @110
    cG
    @122
    reseq2d
    eqtrd
    fveq1d
    @88
    @110
    cB
    @56
    wf
    #
    @111
    @123
    @90
    wceq
    @88
    @95
    @126
    @109
    @88
    @94
    @110
    cB
    @56
    @122
    feq2d
    mpbid
    @121
    @110
    cB
    @55
    cF
    @56
    fvco3
    syl2anc
    @88
    @111
    @125
    @58
    wceq
    @121
    @55
    @110
    cG
    fvres
    syl
    3eqtr3d
    @88
    @79
    @61
    @89
    @91
    wa
    wb
    wph
    @79
    @87
    @81
    adantr
    cB
    @58
    @57
    cF
    fniniseg
    syl
    mpbir2and
    expr
    expr
    a2d
    syld
    expcom
    a2d
    nn0ind
    impd
    mpcom
    syldan
end
