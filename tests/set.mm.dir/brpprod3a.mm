include "cop.mm"
include "cpprod.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "pprodss4v.mm"
include "brel.mm"
include "simprd.mm"
include "elvv.mm"
include "sylib.mm"
include "pm4.71ri.mm"
include "19.41vv.mm"
include "bitr4i.mm"
include "breq2.mm"
include "pm5.32i.mm"
include "2exbii.mm"
include "vex.mm"
include "brpprod.mm"
include "anbi2i.mm"
include "3anass.mm"
include "3bitri.mm"

theorem brpprod3a
  let vz: setvar z
  let vw: setvar w
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume brpprod3.1: |- X e. _V
  assume brpprod3.2: |- Y e. _V
  assume brpprod3.3: |- Z e. _V

  disjoint w z
  disjoint R w
  disjoint R z
  disjoint S w
  disjoint S z
  disjoint X w
  disjoint X z
  disjoint Y w
  disjoint Y z
  disjoint Z w
  disjoint Z z
  assert |- ( <. X , Y >. pprod ( R , S ) Z <-> E. z E. w ( Z = <. z , w >. /\ X R z /\ Y S w ) )

  proof
    cX
    cY
    cop
    #
    cZ
    cR
    cS
    cpprod
    #
    wbr
    #
    cZ
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    @2
    wa
    #
    vw
    wex
    vz
    wex
    #
    @6
    @0
    @5
    @1
    wbr
    #
    wa
    #
    vw
    wex
    vz
    wex
    @6
    cX
    @3
    cR
    wbr
    #
    cY
    @4
    cS
    wbr
    #
    w3a
    #
    vw
    wex
    vz
    wex
    @2
    @6
    vw
    wex
    vz
    wex
    #
    @2
    wa
    @8
    @2
    @14
    @2
    cZ
    cvv
    cvv
    cxp
    #
    wcel
    #
    @14
    @2
    @0
    @15
    wcel
    @16
    @0
    cZ
    @15
    @15
    @1
    cR
    cS
    pprodss4v
    brel
    simprd
    vz
    vw
    cZ
    elvv
    sylib
    pm4.71ri
    @6
    @2
    vz
    vw
    19.41vv
    bitr4i
    @7
    @10
    vz
    vw
    @6
    @2
    @9
    cZ
    @5
    @0
    @1
    breq2
    pm5.32i
    2exbii
    @10
    @13
    vz
    vw
    @10
    @6
    @11
    @12
    wa
    #
    wa
    @13
    @9
    @17
    @6
    cR
    cS
    @4
    cX
    cY
    @3
    brpprod3.1
    brpprod3.2
    vz
    vex
    vw
    vex
    brpprod
    anbi2i
    @6
    @11
    @12
    3anass
    bitr4i
    2exbii
    3bitri
end
