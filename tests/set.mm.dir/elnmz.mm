include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "bibi12d.mm"
include "cbvralv.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "elrab2.mm"

theorem elnmz
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let cN: class N
  let cX: class X
  let cB: class B
  let vu: setvar u
  let vw: setvar w
  let cG: class G
  let cH: class H
  assume elnmz.1: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. S <-> ( y .+ x ) e. S ) }

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint x y
  disjoint y z
  disjoint N z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint X x
  disjoint X y
  disjoint X z
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
  disjoint G y
  disjoint G z
  disjoint N u
  disjoint N w
  disjoint S u
  disjoint S w
  disjoint .+ u
  disjoint .+ w
  disjoint H w
  disjoint H z
  disjoint X u
  disjoint X w
  assert |- ( A e. N <-> ( A e. X /\ A. z e. X ( ( A .+ z ) e. S <-> ( z .+ A ) e. S ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @1
    @0
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vy
    cX
    wral
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
    @8
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
    vx
    cA
    cX
    cN
    @7
    @0
    @8
    c.pl
    co
    #
    cS
    wcel
    #
    @8
    @0
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
    @0
    cA
    wceq
    #
    @14
    @6
    @19
    vy
    vz
    cX
    @1
    @8
    wceq
    #
    @3
    @16
    @5
    @18
    @21
    @2
    @15
    cS
    @1
    @8
    @0
    c.pl
    oveq2
    eleq1d
    @21
    @4
    @17
    cS
    @1
    @8
    @0
    c.pl
    oveq1
    eleq1d
    bibi12d
    cbvralv
    @20
    @19
    @13
    vz
    cX
    @20
    @16
    @10
    @18
    @12
    @20
    @15
    @9
    cS
    @0
    cA
    @8
    c.pl
    oveq1
    eleq1d
    @20
    @17
    @11
    cS
    @0
    cA
    @8
    c.pl
    oveq2
    eleq1d
    bibi12d
    ralbidv
    syl5bb
    elnmz.1
    elrab2
end
