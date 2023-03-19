include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cop.mm"
include "csn.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cii.mm"
include "ccn.mm"
include "ccom.mm"
include "cvmliftlem11.mm"
include "simpld.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "ffun.mm"
include "cfz.mm"
include "cv.mm"
include "ciun.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "fveq2.mm"
include "ssiun2s.mm"
include "syl6sseqr.mm"
include "cmin.mm"
include "cdiv.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "a1i.mm"
include "nnrecred.mm"
include "rexrd.mm"
include "cr.mm"
include "clt.mm"
include "1red.mm"
include "0le1.mm"
include "nnred.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "div0d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "cres.mm"
include "wa.mm"
include "eqid.mm"
include "simpr.mm"
include "cvmliftlem7.mm"
include "cvmliftlem6.mm"
include "mpdan.mm"
include "fdm.mm"
include "funssfv.mm"
include "cvmliftlem9.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "cvmliftlem4.mm"
include "eqtri.mm"
include "fveq12d.mm"
include "3eqtr3d.mm"
include "cn0.mm"
include "0nn0.mm"
include "fvsng.mm"
include "sylancr.mm"
include "3eqtrd.mm"

theorem cvmliftlem13
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
  let cK: class K
  let cL: class L
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
  let cM: class M
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
  assume cvmliftlem.k: |- K = U_ k e. ( 1 ... N ) ( Q ` k )

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
  disjoint M b
  disjoint M c
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint M z
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
  assert |- ( ph -> ( K ` 0 ) = P )

  proof
    wph
    cc0
    cK
    cfv
    #
    cc0
    c1
    cQ
    cfv
    #
    cfv
    #
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
    cK
    wfun
    #
    @1
    cK
    wss
    cc0
    @1
    cdm
    #
    wcel
    @0
    @2
    wceq
    wph
    cc0
    c1
    cicc
    co
    #
    cB
    cK
    wf
    #
    @5
    wph
    cK
    cii
    cC
    ccn
    co
    wcel
    #
    @8
    wph
    @9
    cF
    cK
    ccom
    cG
    wceq
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
    cK
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
    cvmliftlem.k
    cvmliftlem11
    simpld
    cK
    cii
    cC
    @7
    cB
    iiuni
    cvmliftlem.b
    cnf
    syl
    @7
    cB
    cK
    ffun
    syl
    wph
    @1
    vk
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    cQ
    cfv
    #
    ciun
    #
    cK
    wph
    c1
    @10
    wcel
    #
    @1
    @13
    wss
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    @14
    wph
    cN
    cn
    @15
    cvmliftlem.n
    nnuz
    syl6eleq
    c1
    cN
    eluzfz1
    syl
    #
    vk
    @10
    @12
    c1
    @1
    @11
    c1
    cQ
    fveq2
    ssiun2s
    syl
    cvmliftlem.k
    syl6sseqr
    wph
    cc0
    c1
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    c1
    cN
    cdiv
    co
    #
    cicc
    co
    #
    @6
    wph
    cc0
    cc0
    @19
    cicc
    co
    #
    @20
    wph
    cc0
    cxr
    wcel
    #
    @19
    cxr
    wcel
    cc0
    @19
    cle
    wbr
    #
    cc0
    @21
    wcel
    @22
    wph
    0xr
    a1i
    wph
    @19
    wph
    cN
    cvmliftlem.n
    nnrecred
    rexrd
    wph
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    #
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @23
    wph
    1red
    @24
    wph
    0le1
    a1i
    wph
    cN
    cvmliftlem.n
    nnred
    wph
    cN
    cvmliftlem.n
    nngt0d
    c1
    cN
    divge0
    syl22anc
    cc0
    @19
    lbicc2
    syl3anc
    wph
    @18
    cc0
    @19
    cicc
    wph
    @18
    cc0
    cN
    cdiv
    co
    cc0
    @17
    cc0
    cN
    cdiv
    1m1e0
    oveq1i
    wph
    cN
    wph
    cN
    cvmliftlem.n
    nncnd
    wph
    cN
    cvmliftlem.n
    nnne0d
    div0d
    syl5eq
    #
    oveq1d
    eleqtrrd
    wph
    @20
    cB
    @1
    wf
    #
    @6
    @20
    wceq
    wph
    @26
    cF
    @1
    ccom
    cG
    @20
    cres
    wceq
    #
    wph
    @14
    @26
    @27
    wa
    @16
    wph
    @14
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
    c1
    cN
    @20
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
    eqid
    #
    wph
    @14
    simpr
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
    c1
    cN
    @20
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
    @28
    cvmliftlem7
    cvmliftlem6
    mpdan
    simpld
    @20
    cB
    @1
    fdm
    syl
    eleqtrrd
    cc0
    cK
    @1
    funssfv
    syl3anc
    wph
    @18
    @1
    cfv
    #
    @18
    @17
    cQ
    cfv
    #
    cfv
    #
    @2
    @4
    wph
    @14
    @29
    @31
    wceq
    @16
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
    c1
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
    cvmliftlem9
    mpdan
    wph
    @18
    cc0
    @1
    @25
    fveq2d
    wph
    @18
    cc0
    @30
    @3
    @30
    @3
    wceq
    wph
    @30
    cc0
    cQ
    cfv
    @3
    @17
    cc0
    cQ
    1m1e0
    fveq2i
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
    eqtri
    a1i
    @25
    fveq12d
    3eqtr3d
    wph
    cc0
    cn0
    wcel
    cP
    cB
    wcel
    @4
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
    3eqtrd
end
