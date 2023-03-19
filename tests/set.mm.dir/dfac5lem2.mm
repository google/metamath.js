include "cv.mm"
include "cop.mm"
include "cuni.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cab.mm"
include "wel.mm"
include "wex.mm"
include "unieqi.mm"
include "eleq2i.mm"
include "eluniab.mm"
include "r19.42v.mm"
include "anass.mm"
include "bitr2i.mm"
include "exbii.mm"
include "rexcom4.mm"
include "df-rex.mm"
include "bitr3i.mm"
include "3bitri.mm"
include "ancom.mm"
include "ne0i.mm"
include "pm4.71i.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "snex.mm"
include "vex.mm"
include "xpex.mm"
include "eleq2.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "opelxp.mm"
include "velsn.mm"
include "equcom.mm"
include "anbi1i.mm"
include "an12.mm"
include "elequ1.mm"
include "anbi12d.mm"

theorem dfac5lem2
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vg: setvar g
  let vh: setvar h
  let vf: setvar f
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  let vv: setvar v
  let cB: class B
  assume dfac5lem.1: |- A = { u | ( u =/= (/) /\ E. t e. h u = ( { t } X. t ) ) }

  disjoint u w
  disjoint t w
  disjoint h w
  disjoint g w
  disjoint t u
  disjoint h u
  disjoint g u
  disjoint h t
  disjoint g t
  disjoint g h
  disjoint A w
  disjoint A g
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
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint g v
  disjoint B z
  disjoint B w
  disjoint B f
  disjoint B g
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( <. w , g >. e. U. A <-> ( w e. h /\ g e. w ) )

  proof
    vw
    cv
    #
    vg
    cv
    #
    cop
    #
    cA
    cuni
    #
    wcel
    @2
    vu
    cv
    #
    c0
    wne
    #
    @4
    vt
    cv
    #
    csn
    #
    @6
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
    cuni
    #
    wcel
    #
    vt
    vh
    wel
    #
    @2
    @4
    wcel
    #
    @5
    wa
    #
    @9
    wa
    #
    vu
    wex
    #
    wa
    #
    vt
    wex
    #
    vw
    vh
    wel
    #
    vg
    vw
    wel
    #
    wa
    #
    @3
    @14
    @2
    cA
    @13
    dfac5lem.1
    unieqi
    eleq2i
    @15
    @17
    @12
    wa
    #
    vu
    wex
    @19
    vt
    @10
    wrex
    #
    vu
    wex
    #
    @22
    @12
    vu
    @2
    eluniab
    @26
    @27
    vu
    @27
    @18
    @11
    wa
    @26
    @18
    @9
    vt
    @10
    r19.42v
    @17
    @5
    @11
    anass
    bitr2i
    exbii
    @28
    @20
    vt
    @10
    wrex
    @22
    @19
    vt
    vu
    @10
    rexcom4
    @20
    vt
    @10
    df-rex
    bitr3i
    3bitri
    @22
    @6
    @0
    wceq
    #
    @16
    vg
    vt
    wel
    #
    wa
    #
    wa
    #
    vt
    wex
    @25
    @21
    @32
    vt
    @21
    @16
    @2
    @8
    wcel
    #
    wa
    @16
    @29
    @30
    wa
    #
    wa
    @32
    @20
    @33
    @16
    @20
    @9
    @17
    wa
    #
    vu
    wex
    @33
    @19
    @35
    vu
    @19
    @9
    @18
    wa
    @35
    @18
    @9
    ancom
    @17
    @18
    @9
    @17
    @5
    @4
    @2
    ne0i
    pm4.71i
    anbi2i
    bitr4i
    exbii
    @17
    @33
    vu
    @8
    @7
    @6
    @6
    snex
    vt
    vex
    xpex
    @4
    @8
    @2
    eleq2
    ceqsexv
    bitri
    anbi2i
    @33
    @34
    @16
    @33
    @0
    @7
    wcel
    #
    @30
    wa
    @34
    @0
    @1
    @7
    @6
    opelxp
    @36
    @29
    @30
    @36
    @0
    @6
    wceq
    @29
    vw
    @6
    velsn
    vw
    vt
    equcom
    bitri
    anbi1i
    bitri
    anbi2i
    @16
    @29
    @30
    an12
    3bitri
    exbii
    @31
    @25
    vt
    @0
    vw
    vex
    @29
    @16
    @23
    @30
    @24
    vt
    vw
    vh
    elequ1
    @6
    @0
    @1
    eleq2
    anbi12d
    ceqsexv
    bitri
    3bitri
end
