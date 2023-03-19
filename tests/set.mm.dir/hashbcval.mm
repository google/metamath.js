include "wcel.mm"
include "cvv.mm"
include "cn0.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "elex.mm"
include "wa.mm"
include "pwexg.mm"
include "adantr.mm"
include "rabexg.mm"
include "syl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "simpl.mm"
include "pweqd.mm"
include "simpr.mm"
include "eqeq2d.mm"
include "rabeqbidv.mm"
include "syl5eq.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "sylan.mm"

theorem hashbcval
  let vx: setvar x
  let cA: class A
  let cC: class C
  let vi: setvar i
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vy: setvar y
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cF: class F
  let cM: class M
  let cB: class B
  let cR: class R
  let cT: class T
  assume ramval.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )

  disjoint C x
  disjoint a b
  disjoint a i
  disjoint a x
  disjoint b i
  disjoint b x
  disjoint i x
  disjoint A a
  disjoint A i
  disjoint A x
  disjoint N a
  disjoint N i
  disjoint N x
  disjoint V x
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint x y
  disjoint C y
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c s
  disjoint c z
  disjoint F c
  disjoint f m
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f z
  disjoint F f
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a c
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a s
  disjoint a y
  disjoint a z
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b s
  disjoint b y
  disjoint b z
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint f i
  disjoint M f
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint B a
  disjoint B i
  disjoint B x
  disjoint R c
  disjoint R f
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T m
  disjoint T r
  disjoint T y
  disjoint T z
  disjoint V c
  disjoint V f
  disjoint V m
  disjoint V n
  disjoint V r
  disjoint V s
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ N e. NN0 ) -> ( A C N ) = { x e. ~P A | ( # ` x ) = N } )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cN
    cC
    co
    vx
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    wceq
    #
    cA
    cV
    elex
    @0
    @1
    @6
    cvv
    wcel
    #
    @7
    @0
    @1
    wa
    @5
    cvv
    wcel
    #
    @8
    @0
    @9
    @1
    cA
    cvv
    pwexg
    adantr
    @4
    vx
    @5
    cvv
    rabexg
    syl
    va
    vi
    cA
    cN
    cvv
    cn0
    vb
    cv
    #
    chash
    cfv
    #
    vi
    cv
    #
    wceq
    #
    vb
    va
    cv
    #
    cpw
    #
    crab
    #
    @6
    cC
    cvv
    @14
    cA
    wceq
    #
    @12
    cN
    wceq
    #
    wa
    #
    @16
    @3
    @12
    wceq
    #
    vx
    @15
    crab
    @6
    @13
    @20
    vb
    vx
    @15
    @10
    @2
    wceq
    @11
    @3
    @12
    @10
    @2
    chash
    fveq2
    eqeq1d
    cbvrabv
    @19
    @20
    @4
    vx
    @15
    @5
    @19
    @14
    cA
    @17
    @18
    simpl
    pweqd
    @19
    @12
    cN
    @3
    @17
    @18
    simpr
    eqeq2d
    rabeqbidv
    syl5eq
    ramval.c
    ovmpt2ga
    mpd3an3
    sylan
end
