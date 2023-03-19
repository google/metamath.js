include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "fveq2.mm"
include "inf3lemb.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "wne.mm"
include "wa.mm"
include "csuc.mm"
include "wrex.mm"
include "nnsuc.mm"
include "vex.mm"
include "inf3lemc.mm"
include "eleq2d.mm"
include "cin.mm"
include "fvex.mm"
include "inf3lema.mm"
include "simplbi.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "sseq1d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "syl.mm"
include "expcom.mm"
include "pm2.61ine.mm"

theorem inf3lemd
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume inf3lem.1: |- G = ( y e. _V |-> { w e. x | ( w i^i x ) C_ y } )
  assume inf3lem.2: |- F = ( rec ( G , (/) ) |` _om )
  assume inf3lem.3: |- A e. _V
  assume inf3lem.4: |- B e. _V

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  disjoint G v
  disjoint G u
  disjoint G f
  disjoint F v
  disjoint F u
  disjoint F f
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B v
  disjoint B u
  disjoint B f
  assert |- ( A e. _om -> ( F ` A ) C_ x )

  proof
    cA
    com
    wcel
    #
    cA
    cF
    cfv
    #
    vx
    cv
    #
    wss
    #
    wi
    cA
    c0
    cA
    c0
    wceq
    #
    @3
    @0
    @4
    @1
    c0
    @2
    @4
    @1
    c0
    cF
    cfv
    c0
    cA
    c0
    cF
    fveq2
    vx
    vy
    vw
    cA
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.4
    inf3lemb
    syl6eq
    @2
    0ss
    syl6eqss
    a1d
    @0
    cA
    c0
    wne
    #
    @3
    @0
    @5
    wa
    cA
    vv
    cv
    #
    csuc
    #
    wceq
    #
    vv
    com
    wrex
    @3
    vv
    cA
    nnsuc
    @8
    @3
    vv
    com
    @6
    com
    wcel
    #
    @3
    @8
    @7
    cF
    cfv
    #
    @2
    wss
    @9
    vu
    @10
    @2
    @9
    vu
    cv
    #
    @10
    wcel
    @11
    @6
    cF
    cfv
    #
    cG
    cfv
    #
    wcel
    #
    @11
    @2
    wcel
    #
    @9
    @10
    @13
    @11
    vx
    vy
    vw
    @6
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    vv
    vex
    inf3lem.4
    inf3lemc
    eleq2d
    @14
    @15
    @11
    @2
    cin
    @12
    wss
    vx
    vy
    vw
    @11
    @12
    cF
    cG
    inf3lem.1
    inf3lem.2
    vu
    vex
    @6
    cF
    fvex
    inf3lema
    simplbi
    syl6bi
    ssrdv
    @8
    @1
    @10
    @2
    cA
    @7
    cF
    fveq2
    sseq1d
    syl5ibrcom
    rexlimiv
    syl
    expcom
    pm2.61ine
end
