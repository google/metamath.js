include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "wwe.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "cima.mm"
include "wral.mm"
include "zorn2lem1.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "wi.mm"
include "wfn.mm"
include "wss.mm"
include "cvv.mm"
include "wn.mm"
include "crio.mm"
include "cmpt.mm"
include "tfr1.mm"
include "onss.mm"
include "fnfvima.mm"
include "3expia.mm"
include "sylancr.mm"
include "adantr.mm"
include "breq1.mm"
include "rspccv.mm"
include "sylsyld.mm"

theorem zorn2lem2
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
  assert |- ( ( x e. On /\ ( w We A /\ D =/= (/) ) ) -> ( y e. x -> ( F ` y ) R ( F ` x ) ) )

  proof
    vx
    cv
    #
    con0
    wcel
    #
    cA
    vw
    cv
    #
    wwe
    cD
    c0
    wne
    wa
    #
    wa
    #
    vg
    cv
    #
    @0
    cF
    cfv
    #
    cR
    wbr
    #
    vg
    cF
    @0
    cima
    #
    wral
    #
    vy
    cv
    #
    @0
    wcel
    #
    @10
    cF
    cfv
    #
    @8
    wcel
    #
    @12
    @6
    cR
    wbr
    #
    @4
    @6
    cD
    wcel
    #
    @9
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
    @15
    @6
    cA
    wcel
    @9
    @5
    vz
    cv
    #
    cR
    wbr
    #
    vg
    @8
    wral
    @9
    vz
    @6
    cA
    cD
    @16
    @6
    wceq
    @17
    @7
    vg
    @8
    @16
    @6
    @5
    cR
    breq2
    ralbidv
    zorn2lem.5
    elrab2
    simprbi
    syl
    @1
    @11
    @13
    wi
    #
    @3
    @1
    cF
    con0
    wfn
    #
    @0
    con0
    wss
    #
    @18
    cF
    vf
    cvv
    vu
    cv
    vv
    cv
    @2
    wbr
    wn
    vu
    cC
    wral
    vv
    cC
    crio
    cmpt
    zorn2lem.3
    tfr1
    @0
    onss
    @19
    @20
    @11
    @13
    con0
    @0
    cF
    @10
    fnfvima
    3expia
    sylancr
    adantr
    @7
    @14
    vg
    @12
    @8
    @5
    @12
    @6
    cR
    breq1
    rspccv
    sylsyld
end
