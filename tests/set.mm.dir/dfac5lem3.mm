include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cab.mm"
include "wcel.mm"
include "snex.mm"
include "vex.mm"
include "xpex.mm"
include "neeq1.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "elab.mm"
include "eleq2i.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "crn.mm"
include "rneq.mm"
include "snnz.mm"
include "rnxp.mm"
include "ax-mp.mm"
include "rn0.mm"
include "3eqtr3g.mm"
include "impbii.mm"
include "necon3bii.mm"
include "wex.mm"
include "df-rex.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "eqtrd.mm"
include "equcom.mm"
include "bitri.mm"
include "anbi2i.mm"
include "ancom.mm"
include "exbii.mm"
include "elequ1.mm"
include "ceqsexv.mm"
include "3bitrri.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem dfac5lem3
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vh: setvar h
  let vf: setvar f
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  let vv: setvar v
  let vg: setvar g
  let cB: class B
  assume dfac5lem.1: |- A = { u | ( u =/= (/) /\ E. t e. h u = ( { t } X. t ) ) }

  disjoint u w
  disjoint t w
  disjoint h w
  disjoint t u
  disjoint h u
  disjoint h t
  disjoint A w
  disjoint f x
  disjoint f z
  disjoint f y
  disjoint f w
  disjoint f v
  disjoint f u
  disjoint f t
  disjoint f h
  disjoint f g
  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint g x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint g z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint g y
  disjoint v w
  disjoint g w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint g v
  disjoint g u
  disjoint g t
  disjoint g h
  disjoint B z
  disjoint B w
  disjoint B f
  disjoint B g
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A g
  assert |- ( ( { w } X. w ) e. A <-> ( w =/= (/) /\ w e. h ) )

  proof
    vw
    cv
    #
    csn
    #
    @0
    cxp
    #
    vu
    cv
    #
    c0
    wne
    #
    @3
    vt
    cv
    #
    csn
    #
    @5
    cxp
    #
    wceq
    #
    vt
    vh
    cv
    #
    wrex
    #
    wa
    #
    vu
    cab
    #
    wcel
    @2
    c0
    wne
    #
    @2
    @7
    wceq
    #
    vt
    @9
    wrex
    #
    wa
    #
    @2
    cA
    wcel
    @0
    c0
    wne
    #
    @0
    @9
    wcel
    #
    wa
    @11
    @16
    vu
    @2
    @1
    @0
    @0
    snex
    vw
    vex
    #
    xpex
    @3
    @2
    wceq
    #
    @4
    @13
    @10
    @15
    @3
    @2
    c0
    neeq1
    @20
    @8
    @14
    vt
    @9
    @3
    @2
    @7
    eqeq1
    rexbidv
    anbi12d
    elab
    cA
    @12
    @2
    dfac5lem.1
    eleq2i
    @17
    @13
    @18
    @15
    @0
    c0
    @2
    c0
    @0
    c0
    wceq
    #
    @2
    c0
    wceq
    #
    @21
    @2
    @1
    c0
    cxp
    c0
    @0
    c0
    @1
    xpeq2
    @1
    xp0
    syl6eq
    @22
    @2
    crn
    #
    c0
    crn
    @0
    c0
    @2
    c0
    rneq
    @1
    c0
    wne
    @23
    @0
    wceq
    @0
    @19
    snnz
    @1
    @0
    rnxp
    ax-mp
    #
    rn0
    3eqtr3g
    impbii
    necon3bii
    @15
    @5
    @9
    wcel
    #
    @14
    wa
    #
    vt
    wex
    @5
    @0
    wceq
    #
    @25
    wa
    #
    vt
    wex
    @18
    @14
    vt
    @9
    df-rex
    @26
    @28
    vt
    @26
    @25
    @27
    wa
    @28
    @14
    @27
    @25
    @14
    @0
    @5
    wceq
    #
    @27
    @14
    @29
    @14
    @23
    @7
    crn
    #
    @0
    @5
    @2
    @7
    rneq
    @24
    @6
    c0
    wne
    @30
    @5
    wceq
    @5
    vt
    vex
    snnz
    @6
    @5
    rnxp
    ax-mp
    3eqtr3g
    @29
    @2
    @6
    @0
    cxp
    @7
    @29
    @1
    @6
    @0
    @0
    @5
    sneq
    xpeq1d
    @0
    @5
    @6
    xpeq2
    eqtrd
    impbii
    vw
    vt
    equcom
    bitri
    anbi2i
    @25
    @27
    ancom
    bitri
    exbii
    @25
    @18
    vt
    @0
    @19
    vt
    vw
    vh
    elequ1
    ceqsexv
    3bitrri
    anbi12i
    3bitr4i
end
