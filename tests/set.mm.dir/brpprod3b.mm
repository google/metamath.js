include "cop.mm"
include "cpprod.mm"
include "wbr.mm"
include "ccnv.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "pprodcnveq.mm"
include "breqi.mm"
include "opex.mm"
include "brcnv.mm"
include "brpprod3a.mm"
include "bitri.mm"
include "biid.mm"
include "vex.mm"
include "3anbi123i.mm"
include "2exbii.mm"

theorem brpprod3b
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
  assert |- ( X pprod ( R , S ) <. Y , Z >. <-> E. z E. w ( X = <. z , w >. /\ z R Y /\ w S Z ) )

  proof
    cX
    cY
    cZ
    cop
    #
    cR
    cS
    cpprod
    #
    wbr
    cX
    @0
    cR
    ccnv
    #
    cS
    ccnv
    #
    cpprod
    #
    ccnv
    #
    wbr
    #
    cX
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    #
    @7
    cY
    cR
    wbr
    #
    @8
    cZ
    cS
    wbr
    #
    w3a
    #
    vw
    wex
    vz
    wex
    #
    cX
    @0
    @1
    @5
    cR
    cS
    pprodcnveq
    breqi
    @6
    @9
    cY
    @7
    @2
    wbr
    #
    cZ
    @8
    @3
    wbr
    #
    w3a
    #
    vw
    wex
    vz
    wex
    #
    @13
    @6
    @0
    cX
    @4
    wbr
    @17
    cX
    @0
    @4
    brpprod3.1
    cY
    cZ
    opex
    brcnv
    vz
    vw
    @2
    @3
    cY
    cZ
    cX
    brpprod3.2
    brpprod3.3
    brpprod3.1
    brpprod3a
    bitri
    @16
    @12
    vz
    vw
    @9
    @9
    @14
    @10
    @15
    @11
    @9
    biid
    cY
    @7
    cR
    brpprod3.2
    vz
    vex
    brcnv
    cZ
    @8
    cS
    brpprod3.3
    vw
    vex
    brcnv
    3anbi123i
    2exbii
    bitri
    bitri
end
