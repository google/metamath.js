include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "lnoval.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "ralbidv.mm"
include "elrab.mm"
include "cba.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem islno
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cH: class H
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  assume lnoval.1: |- X = ( BaseSet ` U )
  assume lnoval.2: |- Y = ( BaseSet ` W )
  assume lnoval.3: |- G = ( +v ` U )
  assume lnoval.4: |- H = ( +v ` W )
  assume lnoval.5: |- R = ( .sOLD ` U )
  assume lnoval.6: |- S = ( .sOLD ` W )
  assume lnoval.7: |- L = ( U LnOp W )

  disjoint x y
  disjoint x z
  disjoint U x
  disjoint y z
  disjoint U y
  disjoint U z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X y
  disjoint X z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint U t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint U u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint U w
  disjoint W t
  disjoint W u
  disjoint W w
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint Y t
  disjoint Y u
  disjoint Y w
  disjoint G t
  disjoint G u
  disjoint G w
  disjoint R t
  disjoint R u
  disjoint R w
  disjoint H t
  disjoint H u
  disjoint H w
  disjoint S t
  disjoint S u
  disjoint S w
  disjoint T t
  disjoint T u
  disjoint T w
  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. L <-> ( T : X --> Y /\ A. x e. CC A. y e. X A. z e. X ( T ` ( ( x R y ) G z ) ) = ( ( x S ( T ` y ) ) H ( T ` z ) ) ) ) )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    #
    cT
    cL
    wcel
    cT
    vx
    cv
    #
    vy
    cv
    #
    cR
    co
    vz
    cv
    #
    cG
    co
    #
    vw
    cv
    #
    cfv
    #
    @1
    @2
    @5
    cfv
    #
    cS
    co
    #
    @3
    @5
    cfv
    #
    cH
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    vx
    cc
    wral
    #
    vw
    cY
    cX
    cmap
    co
    #
    crab
    #
    wcel
    #
    cX
    cY
    cT
    wf
    #
    @4
    cT
    cfv
    #
    @1
    @2
    cT
    cfv
    #
    cS
    co
    #
    @3
    cT
    cfv
    #
    cH
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    vx
    cc
    wral
    #
    wa
    #
    @0
    cL
    @15
    cT
    vx
    vy
    vz
    vw
    cR
    cS
    cU
    cG
    cH
    cL
    cW
    cX
    cY
    lnoval.1
    lnoval.2
    lnoval.3
    lnoval.4
    lnoval.5
    lnoval.6
    lnoval.7
    lnoval
    eleq2d
    @16
    cT
    @14
    wcel
    #
    @25
    wa
    @26
    @13
    @25
    vw
    cT
    @14
    @5
    cT
    wceq
    #
    @12
    @24
    vx
    cc
    @28
    @11
    @23
    vy
    vz
    cX
    cX
    @28
    @6
    @18
    @10
    @22
    @4
    @5
    cT
    fveq1
    @28
    @8
    @20
    @9
    @21
    cH
    @28
    @7
    @19
    @1
    cS
    @2
    @5
    cT
    fveq1
    oveq2d
    @3
    @5
    cT
    fveq1
    oveq12d
    eqeq12d
    2ralbidv
    ralbidv
    elrab
    @27
    @17
    @25
    cY
    cX
    cT
    cY
    cW
    cba
    cfv
    cvv
    lnoval.2
    cW
    cba
    fvex
    eqeltri
    cX
    cU
    cba
    cfv
    cvv
    lnoval.1
    cU
    cba
    fvex
    eqeltri
    elmap
    anbi1i
    bitri
    syl6bb
end
