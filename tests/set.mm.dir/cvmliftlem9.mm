include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfv.mm"
include "cv.mm"
include "c2nd.mm"
include "crio.mm"
include "cres.mm"
include "ccnv.mm"
include "cicc.mm"
include "cvv.mm"
include "cn.mm"
include "cmpt.mm"
include "wceq.mm"
include "elfznn.mm"
include "eqid.mm"
include "cvmliftlem5.mm"
include "sylan2.mm"
include "simpr.mm"
include "fveq2d.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "adantl.mm"
include "nnred.mm"
include "peano2rem.mm"
include "syl.mm"
include "adantr.mm"
include "nndivred.mm"
include "rexrd.mm"
include "clt.mm"
include "ltm1d.mm"
include "cc0.mm"
include "wb.mm"
include "nngt0d.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "ccvm.mm"
include "c1st.mm"
include "cvmliftlem1.mm"
include "csn.mm"
include "cima.mm"
include "cvmliftlem7.mm"
include "wf.mm"
include "wfn.mm"
include "ccn.mm"
include "cvmcn.mm"
include "cnf.mm"
include "3syl.mm"
include "ffn.mm"
include "fniniseg.mm"
include "simpld.mm"
include "simprd.mm"
include "cvmliftlem3.mm"
include "eqeltrd.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "fvres.mm"
include "eqtrd.mm"
include "wf1o.mm"
include "wi.mm"
include "cvmsf1o.mm"
include "f1ocnvfv.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem cvmliftlem9
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
  let cW: class W
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
  disjoint W k
  disjoint W m
  disjoint W x
  disjoint W z
  assert |- ( ( ph /\ M e. ( 1 ... N ) ) -> ( ( Q ` M ) ` ( ( M - 1 ) / N ) ) = ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) )

  proof
    wph
    cM
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    #
    cM
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cM
    cQ
    cfv
    #
    cfv
    @3
    cG
    cfv
    #
    cF
    @3
    @2
    cQ
    cfv
    cfv
    #
    vb
    cv
    wcel
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
    @6
    @1
    vz
    @3
    vz
    cv
    #
    cG
    cfv
    #
    @11
    cfv
    #
    @12
    @3
    cM
    cN
    cdiv
    co
    #
    cicc
    co
    #
    @4
    cvv
    @0
    wph
    cM
    cn
    wcel
    #
    @4
    vz
    @17
    @15
    cmpt
    wceq
    cM
    cN
    elfznn
    #
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
    cM
    cN
    @17
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
    @17
    eqid
    #
    cvmliftlem5
    sylan2
    @1
    @13
    @3
    wceq
    #
    wa
    #
    @14
    @5
    @11
    @22
    @13
    @3
    cG
    @1
    @21
    simpr
    fveq2d
    fveq2d
    @1
    @3
    cxr
    wcel
    @16
    cxr
    wcel
    @3
    @16
    cle
    wbr
    @3
    @17
    wcel
    @1
    @3
    @1
    @2
    cN
    @1
    cM
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @1
    cM
    @0
    @18
    wph
    @19
    adantl
    nnred
    #
    cM
    peano2rem
    syl
    #
    wph
    cN
    cn
    wcel
    @0
    cvmliftlem.n
    adantr
    #
    nndivred
    #
    rexrd
    @1
    @16
    @1
    cM
    cN
    @25
    @27
    nndivred
    #
    rexrd
    @1
    @3
    @16
    @28
    @29
    @1
    @2
    cM
    clt
    wbr
    #
    @3
    @16
    clt
    wbr
    #
    @1
    cM
    @25
    ltm1d
    @1
    @24
    @23
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @30
    @31
    wb
    @26
    @25
    @1
    cN
    @27
    nnred
    @1
    cN
    @27
    nngt0d
    @2
    cM
    cN
    ltdiv1
    syl112anc
    mpbid
    ltled
    @3
    @16
    lbicc2
    syl3anc
    #
    @1
    @5
    @11
    fvexd
    fvmptd
    @1
    @6
    @10
    cfv
    #
    @5
    wceq
    #
    @12
    @6
    wceq
    #
    @1
    @33
    @6
    cF
    cfv
    #
    @5
    @1
    @6
    @9
    wcel
    #
    @33
    @36
    wceq
    @1
    @9
    @8
    wcel
    #
    @37
    @1
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @8
    @7
    c1st
    cfv
    #
    cS
    cfv
    wcel
    #
    @6
    cB
    wcel
    #
    @36
    @40
    wcel
    @38
    @37
    wa
    wph
    @39
    @0
    cvmliftlem.f
    adantr
    #
    wph
    @0
    vv
    vu
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    cX
    vs
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
    wph
    @0
    simpr
    #
    cvmliftlem1
    #
    @1
    @42
    @36
    @5
    wceq
    #
    @1
    @6
    cF
    ccnv
    @5
    csn
    cima
    wcel
    #
    @42
    @46
    wa
    #
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
    cM
    cN
    @17
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
    @20
    cvmliftlem7
    @1
    cB
    cX
    cF
    wf
    #
    cF
    cB
    wfn
    @47
    @48
    wb
    @1
    @39
    cF
    cC
    cJ
    ccn
    co
    wcel
    @49
    @43
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    cX
    cvmliftlem.b
    cvmliftlem.x
    cnf
    3syl
    cB
    cX
    cF
    ffn
    cB
    @5
    @6
    cF
    fniniseg
    3syl
    mpbid
    #
    simpld
    @1
    @36
    @5
    @40
    @1
    @42
    @46
    @50
    simprd
    #
    wph
    @0
    vv
    vu
    @3
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    @17
    cX
    vs
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
    @44
    @20
    @32
    cvmliftlem3
    eqeltrd
    vb
    vv
    vu
    @6
    cB
    cC
    cS
    @8
    @40
    vk
    cF
    cJ
    @9
    vs
    cvmliftlem.1
    cvmliftlem.b
    @9
    eqid
    cvmsiota
    syl13anc
    #
    simprd
    #
    @6
    @9
    cF
    fvres
    syl
    @51
    eqtrd
    @1
    @9
    @40
    @10
    wf1o
    #
    @37
    @34
    @35
    wi
    @1
    @39
    @41
    @38
    @54
    @43
    @45
    @1
    @38
    @37
    @52
    simpld
    vv
    vu
    @9
    cC
    cS
    @8
    @40
    vk
    cF
    cJ
    vs
    cvmliftlem.1
    cvmsf1o
    syl3anc
    @53
    @9
    @40
    @6
    @5
    @10
    f1ocnvfv
    syl2anc
    mpd
    eqtrd
end
