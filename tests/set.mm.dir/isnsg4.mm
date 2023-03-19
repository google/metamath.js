include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "isnsg.mm"
include "crab.mm"
include "eqcom.mm"
include "eqeq2i.mm"
include "rabid2.mm"
include "3bitri.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem isnsg4
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vw: setvar w
  let cH: class H
  assume elnmz.1: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. S <-> ( y .+ x ) e. S ) }
  assume nmzsubg.2: |- X = ( Base ` G )
  assume nmzsubg.3: |- .+ = ( +g ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint S x
  disjoint S y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint y z
  disjoint G z
  disjoint N u
  disjoint N w
  disjoint N z
  disjoint S u
  disjoint S w
  disjoint S z
  disjoint .+ u
  disjoint .+ w
  disjoint .+ z
  disjoint H w
  disjoint H z
  disjoint X u
  disjoint X w
  disjoint X z
  assert |- ( S e. ( NrmSGrp ` G ) <-> ( S e. ( SubGrp ` G ) /\ N = X ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    cS
    cG
    csubg
    cfv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    cS
    wcel
    @2
    @1
    c.pl
    co
    cS
    wcel
    wb
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    @0
    cN
    cX
    wceq
    #
    wa
    vx
    vy
    c.pl
    cS
    cG
    cX
    nmzsubg.2
    nmzsubg.3
    isnsg
    @5
    @4
    @0
    @5
    cX
    cN
    wceq
    cX
    @3
    vx
    cX
    crab
    #
    wceq
    @4
    cN
    cX
    eqcom
    cN
    @6
    cX
    elnmz.1
    eqeq2i
    @3
    vx
    cX
    rabid2
    3bitri
    anbi2i
    bitr4i
end
