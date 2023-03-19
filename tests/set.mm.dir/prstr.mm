include "cpreset.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "prslem.mm"
include "simprd.mm"
include "3impia.mm"

theorem prstr
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vb: setvar b
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isprs.b: |- B = ( Base ` K )
  assume isprs.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Preset /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( X .<_ Y /\ Y .<_ Z ) ) -> X .<_ Z )

  proof
    cK
    cpreset
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    #
    cX
    cY
    c.le
    wbr
    cY
    cZ
    c.le
    wbr
    wa
    #
    cX
    cZ
    c.le
    wbr
    #
    @0
    @1
    wa
    cX
    cX
    c.le
    wbr
    @2
    @3
    wi
    cB
    cK
    c.le
    cX
    cY
    cZ
    isprs.b
    isprs.l
    prslem
    simprd
    3impia
end
