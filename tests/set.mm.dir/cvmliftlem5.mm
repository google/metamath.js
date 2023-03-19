include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "cv.mm"
include "cdiv.mm"
include "cicc.mm"
include "c2nd.mm"
include "crio.mm"
include "ccnv.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cseq.mm"
include "cz.mm"
include "caddc.mm"
include "cuz.mm"
include "wceq.mm"
include "0z.mm"
include "simpr.mm"
include "nnuz.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "seqm1.mm"
include "sylancr.mm"
include "fveq1i.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "cin.mm"
include "c0.mm"
include "wn.mm"
include "0nnn.mm"
include "disjsn.mm"
include "mpbir.mm"
include "wfn.mm"
include "fnresi.mm"
include "c0ex.mm"
include "snex.mm"
include "fnsn.mm"
include "fvun1.mm"
include "mp3an12.mm"
include "fvresi.mm"
include "adantl.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fvexd.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "fveq12d.mm"
include "eleq1d.mm"
include "riotaeqbidv.mm"
include "reseq2d.mm"
include "cnveqd.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "ovex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "sylan.mm"
include "3eqtrd.mm"

theorem cvmliftlem5
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
  assert |- ( ( ph /\ M e. NN ) -> ( Q ` M ) = ( z e. W |-> ( `' ( F |` ( iota_ b e. ( 2nd ` ( T ` M ) ) ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) e. b ) ) ` ( G ` z ) ) ) )

  proof
    wph
    cM
    cn
    wcel
    #
    wa
    #
    cM
    cQ
    cfv
    #
    cM
    c1
    cmin
    co
    #
    cQ
    cfv
    #
    cM
    cid
    cn
    cres
    #
    cc0
    cc0
    cP
    cop
    #
    csn
    #
    cop
    csn
    #
    cun
    #
    cfv
    #
    vx
    vm
    cvv
    cn
    vz
    vm
    cv
    #
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    @11
    cN
    cdiv
    co
    #
    cicc
    co
    #
    vz
    cv
    cG
    cfv
    #
    cF
    @13
    vx
    cv
    #
    cfv
    #
    vb
    cv
    #
    wcel
    #
    vb
    @11
    cT
    cfv
    #
    c2nd
    cfv
    #
    crio
    #
    cres
    #
    ccnv
    #
    cfv
    #
    cmpt
    #
    cmpt2
    #
    co
    #
    @4
    cM
    @28
    co
    #
    vz
    cW
    @16
    cF
    @3
    cN
    cdiv
    co
    #
    @4
    cfv
    #
    @19
    wcel
    #
    vb
    cM
    cT
    cfv
    #
    c2nd
    cfv
    #
    crio
    #
    cres
    #
    ccnv
    #
    cfv
    #
    cmpt
    #
    @1
    cM
    @28
    @9
    cc0
    cseq
    #
    cfv
    #
    @3
    @41
    cfv
    #
    @10
    @28
    co
    #
    @2
    @29
    @1
    cc0
    cz
    wcel
    cM
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @42
    @44
    wceq
    0z
    @1
    cM
    cn
    @46
    wph
    @0
    simpr
    #
    cn
    c1
    cuz
    cfv
    @46
    nnuz
    c1
    @45
    cuz
    1e0p1
    fveq2i
    eqtri
    syl6eleq
    @28
    @9
    cc0
    cM
    seqm1
    sylancr
    cM
    cQ
    @41
    cvmliftlem.q
    fveq1i
    @4
    @43
    @10
    @28
    @3
    cQ
    @41
    cvmliftlem.q
    fveq1i
    oveq1i
    3eqtr4g
    @1
    @10
    cM
    @4
    @28
    @1
    @10
    cM
    @5
    cfv
    #
    cM
    @1
    cn
    cc0
    csn
    #
    cin
    c0
    wceq
    #
    @0
    @10
    @48
    wceq
    #
    @50
    cc0
    cn
    wcel
    wn
    0nnn
    cn
    cc0
    disjsn
    mpbir
    @47
    @5
    cn
    wfn
    @8
    @49
    wfn
    @50
    @0
    wa
    @51
    cn
    fnresi
    cc0
    @7
    c0ex
    @6
    snex
    fnsn
    cn
    @49
    @5
    @8
    cM
    fvun1
    mp3an12
    sylancr
    @0
    @48
    cM
    wceq
    wph
    cn
    cM
    fvresi
    adantl
    eqtrd
    oveq2d
    wph
    @4
    cvv
    wcel
    @0
    @30
    @40
    wceq
    wph
    @3
    cQ
    fvexd
    vx
    vm
    @4
    cM
    cvv
    cn
    @27
    @40
    @28
    @17
    @4
    wceq
    #
    @11
    cM
    wceq
    #
    wa
    #
    vz
    @15
    @26
    cW
    @39
    @54
    @15
    @31
    cM
    cN
    cdiv
    co
    #
    cicc
    co
    #
    cW
    @54
    @13
    @31
    @14
    @55
    cicc
    @54
    @12
    @3
    cN
    cdiv
    @54
    @11
    cM
    c1
    cmin
    @52
    @53
    simpr
    #
    oveq1d
    oveq1d
    #
    @54
    @11
    cM
    cN
    cdiv
    @57
    oveq1d
    oveq12d
    cvmliftlem5.3
    syl6eqr
    @54
    @16
    @25
    @38
    @54
    @24
    @37
    @54
    @23
    @36
    cF
    @54
    @20
    @33
    vb
    @22
    @35
    @54
    @21
    @34
    c2nd
    @54
    @11
    cM
    cT
    @57
    fveq2d
    fveq2d
    @54
    @18
    @32
    @19
    @54
    @13
    @31
    @17
    @4
    @52
    @53
    simpl
    @58
    fveq12d
    eleq1d
    riotaeqbidv
    reseq2d
    cnveqd
    fveq1d
    mpteq12dv
    @28
    eqid
    vz
    cW
    @39
    cW
    @56
    cvv
    cvmliftlem5.3
    @31
    @55
    cicc
    ovex
    eqeltri
    mptex
    ovmpt2a
    sylan
    3eqtrd
end
