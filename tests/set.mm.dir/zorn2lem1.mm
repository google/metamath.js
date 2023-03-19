include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "wwe.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "crio.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "tfr2.mm"
include "adantr.mm"
include "wfun.mm"
include "wfn.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "vex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "crn.mm"
include "crab.mm"
include "cima.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "imbi1d.mm"
include "ralbidv2.mm"
include "rabbidv.mm"
include "3eqtr4g.mm"
include "riotaeqbidv.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "syl6eq.mm"
include "wreu.mm"
include "wss.mm"
include "simprl.mm"
include "wor.mm"
include "weso.mm"
include "ad2antrl.mm"
include "soex.mm"
include "sylancl.mm"
include "rabexd.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "simprr.mm"
include "wereu.mm"
include "syl13anc.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem zorn2lem1
  let vx: setvar x
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
  let vy: setvar y
  assume zorn2lem.3: |- F = recs ( ( f e. _V |-> ( iota_ v e. C A. u e. C -. u w v ) ) )
  assume zorn2lem.4: |- C = { z e. A | A. g e. ran f g R z }
  assume zorn2lem.5: |- D = { z e. A | A. g e. ( F " x ) g R z }

  disjoint f g
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint F f
  disjoint F g
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F z
  disjoint R f
  disjoint R g
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
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
  disjoint f y
  disjoint g r
  disjoint g s
  disjoint g y
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
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint D a
  disjoint D b
  disjoint D y
  disjoint F a
  disjoint F b
  disjoint F r
  disjoint F s
  disjoint F y
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R y
  assert |- ( ( x e. On /\ ( w We A /\ D =/= (/) ) ) -> ( F ` x ) e. D )

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
    #
    cD
    c0
    wne
    #
    wa
    #
    wa
    #
    @0
    cF
    cfv
    #
    vu
    cv
    #
    vv
    cv
    @2
    wbr
    wn
    #
    vu
    cD
    wral
    #
    vv
    cD
    crio
    #
    cD
    @6
    @7
    cF
    @0
    cres
    #
    vf
    cvv
    @9
    vu
    cC
    wral
    #
    vv
    cC
    crio
    #
    cmpt
    #
    cfv
    #
    @11
    @1
    @7
    @16
    wceq
    @5
    @0
    cF
    @15
    zorn2lem.3
    tfr2
    adantr
    @12
    cvv
    wcel
    #
    @16
    @11
    wceq
    cF
    wfun
    #
    @0
    cvv
    wcel
    @17
    cF
    con0
    wfn
    @18
    cF
    @15
    zorn2lem.3
    tfr1
    con0
    cF
    fnfun
    ax-mp
    vx
    vex
    cF
    @0
    cvv
    resfunexg
    mp2an
    vf
    @12
    @14
    @11
    cvv
    @15
    vf
    cv
    #
    @12
    wceq
    #
    @13
    @10
    vv
    cC
    cD
    @20
    vg
    cv
    #
    vz
    cv
    cR
    wbr
    #
    vg
    @19
    crn
    #
    wral
    #
    vz
    cA
    crab
    @22
    vg
    cF
    @0
    cima
    #
    wral
    #
    vz
    cA
    crab
    #
    cC
    cD
    @20
    @24
    @26
    vz
    cA
    @20
    @22
    @22
    vg
    @23
    @25
    @20
    @21
    @23
    wcel
    @21
    @25
    wcel
    @22
    @20
    @23
    @25
    @21
    @20
    @23
    @12
    crn
    @25
    @19
    @12
    rneq
    cF
    @0
    df-ima
    syl6eqr
    eleq2d
    imbi1d
    ralbidv2
    rabbidv
    zorn2lem.4
    zorn2lem.5
    3eqtr4g
    #
    @20
    @9
    @9
    vu
    cC
    cD
    @20
    @8
    cC
    wcel
    @8
    cD
    wcel
    @9
    @20
    cC
    cD
    @8
    @28
    eleq2d
    imbi1d
    ralbidv2
    riotaeqbidv
    @15
    eqid
    @10
    vv
    cD
    riotaex
    fvmpt
    ax-mp
    syl6eq
    @6
    @10
    vv
    cD
    wreu
    #
    @11
    cD
    wcel
    @6
    @3
    cD
    cvv
    wcel
    cD
    cA
    wss
    #
    @4
    @29
    @1
    @3
    @4
    simprl
    @6
    @26
    vz
    cA
    cD
    cvv
    zorn2lem.5
    @6
    cA
    @2
    wor
    #
    @2
    cvv
    wcel
    cA
    cvv
    wcel
    @3
    @31
    @1
    @4
    cA
    @2
    weso
    ad2antrl
    vw
    vex
    cA
    @2
    cvv
    soex
    sylancl
    rabexd
    @30
    @6
    cD
    @27
    cA
    zorn2lem.5
    @26
    vz
    cA
    ssrab2
    eqsstri
    a1i
    @1
    @3
    @4
    simprr
    vv
    vu
    cA
    cD
    @2
    cvv
    wereu
    syl13anc
    @10
    vv
    cD
    riotacl
    syl
    eqeltrd
end
