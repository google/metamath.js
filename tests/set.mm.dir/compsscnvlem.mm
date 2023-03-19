include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "simpr.mm"
include "difss.mm"
include "syl6eqss.mm"
include "selpw.mm"
include "sylibr.mm"
include "difeq2d.mm"
include "elpwi.mm"
include "adantr.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqtr2d.mm"
include "jca.mm"

theorem compsscnvlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cX: class X
  let cG: class G

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( ( x e. ~P A /\ y = ( A \ x ) ) -> ( y e. ~P A /\ x = ( A \ y ) ) )

  proof
    vx
    cv
    #
    cA
    cpw
    #
    wcel
    #
    vy
    cv
    #
    cA
    @0
    cdif
    #
    wceq
    #
    wa
    #
    @3
    @1
    wcel
    #
    @0
    cA
    @3
    cdif
    #
    wceq
    @6
    @3
    cA
    wss
    @7
    @6
    @3
    @4
    cA
    @2
    @5
    simpr
    #
    cA
    @0
    difss
    syl6eqss
    vy
    cA
    selpw
    sylibr
    @6
    @8
    cA
    @4
    cdif
    #
    @0
    @6
    @3
    @4
    cA
    @9
    difeq2d
    @6
    @0
    cA
    wss
    #
    @10
    @0
    wceq
    @2
    @11
    @5
    @0
    cA
    elpwi
    adantr
    @0
    cA
    dfss4
    sylib
    eqtr2d
    jca
end
