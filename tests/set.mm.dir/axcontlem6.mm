include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "eqid.mm"
include "axcontlem1.mm"
include "axcontlem5.mm"
include "mpbii.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "sylib.mm"

theorem axcontlem6
  let vx: setvar x
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cU: class U
  let vi: setvar i
  let cF: class F
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cT: class T
  assume axcontlem5.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }
  assume axcontlem5.2: |- F = { <. x , t >. | ( x e. D /\ ( t e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( x ` i ) = ( ( ( 1 - t ) x. ( Z ` i ) ) + ( t x. ( U ` i ) ) ) ) ) }

  disjoint F i
  disjoint D t
  disjoint t x
  disjoint D x
  disjoint i p
  disjoint i t
  disjoint i x
  disjoint N i
  disjoint p t
  disjoint p x
  disjoint N p
  disjoint N t
  disjoint N x
  disjoint P i
  disjoint P t
  disjoint P x
  disjoint U i
  disjoint U p
  disjoint U t
  disjoint U x
  disjoint Z i
  disjoint Z p
  disjoint Z t
  disjoint Z x
  disjoint D s
  disjoint D y
  disjoint F j
  disjoint F s
  disjoint i j
  disjoint i s
  disjoint j s
  disjoint F y
  disjoint i y
  disjoint j p
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint N j
  disjoint N s
  disjoint N y
  disjoint P j
  disjoint P s
  disjoint p s
  disjoint p y
  disjoint P y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t y
  disjoint U j
  disjoint U s
  disjoint U y
  disjoint x y
  disjoint Z j
  disjoint Z s
  disjoint Z y
  disjoint T x
  disjoint T i
  disjoint T t
  assert |- ( ( ( ( N e. NN /\ Z e. ( EE ` N ) /\ U e. ( EE ` N ) ) /\ Z =/= U ) /\ P e. D ) -> ( ( F ` P ) e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( P ` i ) = ( ( ( 1 - ( F ` P ) ) x. ( Z ` i ) ) + ( ( F ` P ) x. ( U ` i ) ) ) ) )

  proof
    cN
    cn
    wcel
    cZ
    cN
    cee
    cfv
    #
    wcel
    cU
    @0
    wcel
    w3a
    cZ
    cU
    wne
    wa
    cP
    cD
    wcel
    wa
    #
    cP
    cF
    cfv
    #
    cc0
    cpnf
    cico
    co
    wcel
    #
    vj
    cv
    #
    cP
    cfv
    #
    c1
    @2
    cmin
    co
    #
    @4
    cZ
    cfv
    #
    cmul
    co
    #
    @2
    @4
    cU
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vj
    c1
    cN
    cfz
    co
    #
    wral
    #
    wa
    #
    @3
    vi
    cv
    #
    cP
    cfv
    #
    @6
    @16
    cZ
    cfv
    #
    cmul
    co
    #
    @2
    @16
    cU
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @13
    wral
    #
    wa
    @1
    @2
    @2
    wceq
    @15
    @2
    eqid
    vy
    vs
    cD
    cP
    @2
    cU
    vj
    cF
    cN
    cZ
    vp
    axcontlem5.1
    vx
    vy
    vt
    cD
    cU
    vi
    vj
    cF
    cN
    cZ
    vs
    axcontlem5.2
    axcontlem1
    axcontlem5
    mpbii
    @14
    @24
    @3
    @12
    @23
    vj
    vi
    @13
    @4
    @16
    wceq
    #
    @5
    @17
    @11
    @22
    @4
    @16
    cP
    fveq2
    @25
    @8
    @19
    @10
    @21
    caddc
    @25
    @7
    @18
    @6
    cmul
    @4
    @16
    cZ
    fveq2
    oveq2d
    @25
    @9
    @20
    @2
    cmul
    @4
    @16
    cU
    fveq2
    oveq2d
    oveq12d
    eqeq12d
    cbvralv
    anbi2i
    sylib
end
