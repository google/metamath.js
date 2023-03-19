include "wpo.mm"
include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "wwe.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "zorn2lem2.mm"
include "adantl.mm"
include "cima.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zorn2lem1.mm"
include "sseldi.mm"
include "breq1.mm"
include "biimprcd.mm"
include "poirr.mm"
include "nsyli.mm"
include "com12.mm"
include "sylan2.mm"
include "syld.mm"

theorem zorn2lem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  assume zorn2lem.3: |- F = recs ( ( f e. _V |-> ( iota_ v e. C A. u e. C -. u w v ) ) )
  assume zorn2lem.4: |- C = { z e. A | A. g e. ran f g R z }
  assume zorn2lem.5: |- D = { z e. A | A. g e. ( F " x ) g R z }

  disjoint f g
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint F f
  disjoint F g
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R f
  disjoint R g
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C v
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f r
  disjoint f s
  disjoint g r
  disjoint g s
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint D a
  disjoint D b
  disjoint F a
  disjoint F b
  disjoint F r
  disjoint F s
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  assert |- ( ( R Po A /\ ( x e. On /\ ( w We A /\ D =/= (/) ) ) ) -> ( y e. x -> -. ( F ` x ) = ( F ` y ) ) )

  proof
    cA
    cR
    wpo
    #
    vx
    cv
    #
    con0
    wcel
    cA
    vw
    cv
    wwe
    cD
    c0
    wne
    wa
    wa
    #
    wa
    vy
    cv
    #
    @1
    wcel
    #
    @3
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    cR
    wbr
    #
    @6
    @5
    wceq
    #
    wn
    #
    @2
    @4
    @7
    wi
    @0
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cC
    cD
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    zorn2lem.5
    zorn2lem2
    adantl
    @2
    @0
    @6
    cA
    wcel
    #
    @7
    @9
    wi
    @2
    cD
    cA
    @6
    cD
    vg
    cv
    vz
    cv
    cR
    wbr
    vg
    cF
    @1
    cima
    wral
    #
    vz
    cA
    crab
    cA
    zorn2lem.5
    @11
    vz
    cA
    ssrab2
    eqsstri
    vx
    vz
    vw
    vv
    vu
    cA
    cC
    cD
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    zorn2lem.5
    zorn2lem1
    sseldi
    @7
    @0
    @10
    wa
    #
    @9
    @7
    @8
    @6
    @6
    cR
    wbr
    #
    @12
    @8
    @13
    @7
    @6
    @5
    @6
    cR
    breq1
    biimprcd
    cA
    @6
    cR
    poirr
    nsyli
    com12
    sylan2
    syld
end
