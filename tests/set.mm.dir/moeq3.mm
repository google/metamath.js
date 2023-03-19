include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "w3o.mm"
include "wmo.mm"
include "weu.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "biidd.mm"
include "3orbi123d.mm"
include "eubidv.mm"
include "vex.mm"
include "eueq3.mm"
include "vtoclg.mm"
include "eumo.mm"
include "syl.mm"
include "wi.mm"
include "wal.mm"
include "eqvisset.mm"
include "pm2.21.mm"
include "syl5.mm"
include "anim2d.mm"
include "orim1d.mm"
include "3orass.mm"
include "3imtr4g.mm"
include "alrimiv.mm"
include "euimmo.mm"
include "mpisyl.mm"
include "pm2.61i.mm"

theorem moeq3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume moeq3.1: |- B e. _V
  assume moeq3.2: |- C e. _V
  assume moeq3.3: |- -. ( ph /\ ps )

  disjoint ph x
  disjoint ps x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint x y
  disjoint ph y
  disjoint ps y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- E* x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B ) \/ ( ps /\ x = C ) )

  proof
    cA
    cvv
    wcel
    #
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wa
    #
    wph
    wps
    wo
    wn
    @1
    cB
    wceq
    wa
    #
    wps
    @1
    cC
    wceq
    wa
    #
    w3o
    #
    vx
    wmo
    #
    @0
    @6
    vx
    weu
    #
    @7
    wph
    @1
    vy
    cv
    #
    wceq
    #
    wa
    #
    @4
    @5
    w3o
    #
    vx
    weu
    #
    @8
    vy
    cA
    cvv
    @9
    cA
    wceq
    #
    @12
    @6
    vx
    @14
    @11
    @3
    @4
    @4
    @5
    @5
    @14
    @10
    @2
    wph
    @9
    cA
    @1
    eqeq2
    anbi2d
    @14
    @4
    biidd
    @14
    @5
    biidd
    3orbi123d
    eubidv
    wph
    wps
    vx
    @9
    cB
    cC
    vy
    vex
    moeq3.1
    moeq3.2
    moeq3.3
    eueq3
    #
    vtoclg
    @6
    vx
    eumo
    syl
    @0
    wn
    #
    @6
    @12
    wi
    #
    vx
    wal
    @13
    @7
    @16
    @17
    vx
    @16
    @3
    @4
    @5
    wo
    #
    wo
    @11
    @18
    wo
    @6
    @12
    @16
    @3
    @11
    @18
    @16
    @2
    @10
    wph
    @2
    @0
    @16
    @10
    vx
    cA
    eqvisset
    @0
    @10
    pm2.21
    syl5
    anim2d
    orim1d
    @3
    @4
    @5
    3orass
    @11
    @4
    @5
    3orass
    3imtr4g
    alrimiv
    @15
    @6
    @12
    vx
    euimmo
    mpisyl
    pm2.61i
end
