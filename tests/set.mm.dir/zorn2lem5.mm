include "cv.mm"
include "wwe.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cima.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfun.mm"
include "wfn.mm"
include "cvv.mm"
include "wbr.mm"
include "wn.mm"
include "crio.mm"
include "cmpt.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "onelon.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zorn2lem1.mm"
include "sseldi.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "sylani.mm"
include "com12.mm"
include "exp43.mm"
include "com3r.mm"
include "imp.mm"
include "a2d.mm"
include "spsd.mm"
include "syl5bi.mm"
include "rexlimd.mm"
include "syl5.mm"
include "ssrdv.mm"

theorem zorn2lem5
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
  let cH: class H
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume zorn2lem.3: |- F = recs ( ( f e. _V |-> ( iota_ v e. C A. u e. C -. u w v ) ) )
  assume zorn2lem.4: |- C = { z e. A | A. g e. ran f g R z }
  assume zorn2lem.5: |- D = { z e. A | A. g e. ( F " x ) g R z }
  assume zorn2lem.7: |- H = { z e. A | A. g e. ( F " y ) g R z }

  disjoint u x
  disjoint v x
  disjoint f x
  disjoint H x
  disjoint u v
  disjoint f u
  disjoint H u
  disjoint f v
  disjoint H v
  disjoint H f
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
  disjoint s x
  disjoint r x
  disjoint a x
  disjoint b x
  disjoint s u
  disjoint r u
  disjoint a u
  disjoint b u
  disjoint s v
  disjoint r v
  disjoint a v
  disjoint b v
  disjoint f s
  disjoint f r
  disjoint a f
  disjoint b f
  disjoint r s
  disjoint a s
  disjoint b s
  disjoint H s
  disjoint a r
  disjoint b r
  disjoint H r
  disjoint a b
  disjoint H a
  disjoint H b
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
  assert |- ( ( ( w We A /\ x e. On ) /\ A. y e. x H =/= (/) ) -> ( F " x ) C_ A )

  proof
    cA
    vw
    cv
    #
    wwe
    #
    vx
    cv
    #
    con0
    wcel
    #
    wa
    #
    cH
    c0
    wne
    #
    vy
    @2
    wral
    #
    wa
    #
    vs
    cF
    @2
    cima
    #
    cA
    vs
    cv
    #
    @8
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    #
    @9
    wceq
    #
    vy
    @2
    wrex
    #
    @7
    @9
    cA
    wcel
    #
    cF
    wfun
    #
    @10
    @14
    cF
    con0
    wfn
    @16
    cF
    vf
    cvv
    vu
    cv
    vv
    cv
    @0
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
    con0
    cF
    fnfun
    ax-mp
    vy
    @9
    @2
    cF
    fvelima
    mpan
    @7
    @13
    @15
    vy
    @2
    @4
    @6
    vy
    @4
    vy
    nfv
    @5
    vy
    @2
    nfra1
    nfan
    @15
    vy
    nfv
    @4
    @6
    @11
    @2
    wcel
    #
    @13
    @15
    wi
    #
    wi
    #
    @6
    @17
    @5
    wi
    #
    vy
    wal
    @4
    @19
    @5
    vy
    @2
    df-ral
    @4
    @20
    @19
    vy
    @4
    @17
    @5
    @18
    @1
    @3
    @17
    @5
    @18
    wi
    #
    wi
    @3
    @17
    @1
    @21
    @3
    @17
    @1
    @5
    @18
    @13
    @3
    @17
    wa
    #
    @1
    @5
    wa
    #
    wa
    @15
    @22
    @13
    @11
    con0
    wcel
    #
    @23
    @15
    @2
    @11
    onelon
    @24
    @23
    wa
    #
    @12
    cA
    wcel
    @13
    @15
    @25
    cH
    cA
    @12
    cH
    vg
    cv
    vz
    cv
    cR
    wbr
    vg
    cF
    @11
    cima
    wral
    #
    vz
    cA
    crab
    cA
    zorn2lem.7
    @26
    vz
    cA
    ssrab2
    eqsstri
    vy
    vz
    vw
    vv
    vu
    cA
    cC
    cH
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    zorn2lem.7
    zorn2lem1
    sseldi
    @12
    @9
    cA
    eleq1
    syl5ib
    sylani
    com12
    exp43
    com3r
    imp
    a2d
    spsd
    syl5bi
    imp
    rexlimd
    syl5
    ssrdv
end
