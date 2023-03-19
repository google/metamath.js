include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "mndid.mm"
include "mgmidmo.mm"
include "a1i.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem mndideu
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
  assert |- ( G e. Mnd -> E! u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x ) )

  proof
    cG
    cmnd
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    c.pl
    co
    @2
    wceq
    @2
    @1
    c.pl
    co
    @2
    wceq
    wa
    vx
    cB
    wral
    #
    vu
    cB
    wrex
    @3
    vu
    cB
    wrmo
    #
    @3
    vu
    cB
    wreu
    vx
    vu
    cB
    c.pl
    cG
    mndcl.b
    mndcl.p
    mndid
    @4
    @0
    vx
    vu
    cB
    c.pl
    mgmidmo
    a1i
    @3
    vu
    cB
    reu5
    sylanbrc
end
