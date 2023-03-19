include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "ismnd.mm"
include "simprbi.mm"

theorem mndid
  let vx: setvar x
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mndcl.b: |- B = ( Base ` G )
  assume mndcl.p: |- .+ = ( +g ` G )

  disjoint B x
  disjoint G x
  disjoint .+ x
  disjoint u x
  disjoint B u
  disjoint G u
  disjoint .+ u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint Z z
  disjoint .+ y
  disjoint .+ z
  disjoint u y
  disjoint u z
  assert |- ( G e. Mnd -> E. u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x ) )

  proof
    cG
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cB
    wcel
    @2
    vz
    cv
    #
    c.pl
    co
    @0
    @1
    @3
    c.pl
    co
    c.pl
    co
    wceq
    vz
    cB
    wral
    wa
    vy
    cB
    wral
    vx
    cB
    wral
    vu
    cv
    #
    @0
    c.pl
    co
    @0
    wceq
    @0
    @4
    c.pl
    co
    @0
    wceq
    wa
    vx
    cB
    wral
    vu
    cB
    wrex
    cB
    c.pl
    vu
    cG
    vx
    vy
    vz
    mndcl.b
    mndcl.p
    ismnd
    simprbi
end
