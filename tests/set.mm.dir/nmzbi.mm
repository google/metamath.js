include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "elnmz.mm"
include "simprbi.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "bibi12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem nmzbi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cN: class N
  let cX: class X
  let vz: setvar z
  let vu: setvar u
  let vw: setvar w
  let cG: class G
  let cH: class H
  assume elnmz.1: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. S <-> ( y .+ x ) e. S ) }

  disjoint A x
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  disjoint x z
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
  disjoint G x
  disjoint y z
  disjoint G y
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
  assert |- ( ( A e. N /\ B e. X ) -> ( ( A .+ B ) e. S <-> ( B .+ A ) e. S ) )

  proof
    cA
    cN
    wcel
    #
    cA
    vz
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @1
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vz
    cX
    wral
    #
    cB
    cX
    wcel
    cA
    cB
    c.pl
    co
    #
    cS
    wcel
    #
    cB
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    @0
    cA
    cX
    wcel
    @7
    vx
    vy
    vz
    cA
    c.pl
    cS
    cN
    cX
    elnmz.1
    elnmz
    simprbi
    @6
    @12
    vz
    cB
    cX
    @1
    cB
    wceq
    #
    @3
    @9
    @5
    @11
    @13
    @2
    @8
    cS
    @1
    cB
    cA
    c.pl
    oveq2
    eleq1d
    @13
    @4
    @10
    cS
    @1
    cB
    cA
    c.pl
    oveq1
    eleq1d
    bibi12d
    rspccva
    sylan
end
