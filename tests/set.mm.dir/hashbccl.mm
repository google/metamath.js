include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "hashbcval.mm"
include "wss.mm"
include "simpl.mm"
include "pwfi.mm"
include "sylib.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eqeltrd.mm"

theorem hashbccl
  let cA: class A
  let cC: class C
  let vi: setvar i
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x
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
  let cV: class V
  assume ramval.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )

  disjoint a b
  disjoint a i
  disjoint b i
  disjoint A a
  disjoint A i
  disjoint N a
  disjoint N i
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint x y
  disjoint C x
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
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b s
  disjoint b x
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
  disjoint i x
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
  disjoint A x
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
  disjoint N x
  disjoint V c
  disjoint V f
  disjoint V m
  disjoint V n
  disjoint V r
  disjoint V s
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( A e. Fin /\ N e. NN0 ) -> ( A C N ) e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cN
    cC
    co
    vx
    cv
    chash
    cfv
    cN
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    cfn
    vx
    cA
    cC
    vi
    cN
    cfn
    va
    vb
    ramval.c
    hashbcval
    @2
    @4
    cfn
    wcel
    #
    @5
    @4
    wss
    @5
    cfn
    wcel
    @2
    @0
    @6
    @0
    @1
    simpl
    cA
    pwfi
    sylib
    @3
    vx
    @4
    ssrab2
    @4
    @5
    ssfi
    sylancl
    eqeltrd
end
