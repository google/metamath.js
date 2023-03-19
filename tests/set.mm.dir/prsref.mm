include "cpreset.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "id.mm"
include "3jca.mm"
include "prslem.mm"
include "sylan2.mm"
include "simpld.mm"

theorem prsref
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vf: setvar f
  let vb: setvar b
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  let cZ: class Z
  assume isprs.b: |- B = ( Base ` K )
  assume isprs.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Preset /\ X e. B ) -> X .<_ X )

  proof
    cK
    cpreset
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cX
    cX
    c.le
    wbr
    #
    @2
    @2
    wa
    @2
    wi
    #
    @1
    @0
    @1
    @1
    @1
    w3a
    @2
    @3
    wa
    @1
    @1
    @1
    @1
    @1
    id
    #
    @4
    @4
    3jca
    cB
    cK
    c.le
    cX
    cX
    cX
    isprs.b
    isprs.l
    prslem
    sylan2
    simpld
end
