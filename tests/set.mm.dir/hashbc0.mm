include "wcel.mm"
include "cc0.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "c0.mm"
include "csn.mm"
include "cn0.mm"
include "0nn0.mm"
include "hashbcval.mm"
include "mpan2.mm"
include "wa.mm"
include "cab.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "id.mm"
include "0elpw.mm"
include "syl6eqel.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"
include "abbii.mm"
include "df-rab.mm"
include "df-sn.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"

theorem hashbc0
  let cA: class A
  let cC: class C
  let vi: setvar i
  let cV: class V
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
  let cN: class N
  assume ramval.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )

  disjoint a b
  disjoint a i
  disjoint b i
  disjoint A a
  disjoint A i
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
  disjoint N a
  disjoint N i
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
  assert |- ( A e. V -> ( A C 0 ) = { (/) } )

  proof
    cA
    cV
    wcel
    #
    cA
    cc0
    cC
    co
    #
    vx
    cv
    #
    chash
    cfv
    cc0
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    c0
    csn
    #
    @0
    cc0
    cn0
    wcel
    @1
    @5
    wceq
    0nn0
    vx
    cA
    cC
    vi
    cc0
    cV
    va
    vb
    ramval.c
    hashbcval
    mpan2
    @2
    @4
    wcel
    #
    @3
    wa
    #
    vx
    cab
    @2
    c0
    wceq
    #
    vx
    cab
    @5
    @6
    @8
    @9
    vx
    @8
    @7
    @9
    wa
    @9
    @3
    @9
    @7
    @2
    cvv
    wcel
    @3
    @9
    wb
    vx
    vex
    @2
    cvv
    hasheq0
    ax-mp
    anbi2i
    @9
    @7
    @9
    @2
    c0
    @4
    @9
    id
    cA
    0elpw
    syl6eqel
    pm4.71ri
    bitr4i
    abbii
    @3
    vx
    @4
    df-rab
    vx
    c0
    df-sn
    3eqtr4i
    syl6eq
end
