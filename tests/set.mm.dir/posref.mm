include "cpo.mm"
include "wcel.mm"
include "cpreset.mm"
include "wbr.mm"
include "posprs.mm"
include "prsref.mm"
include "sylan.mm"

theorem posref
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  let cZ: class Z
  assume posi.b: |- B = ( Base ` K )
  assume posi.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Poset /\ X e. B ) -> X .<_ X )

  proof
    cK
    cpo
    wcel
    cK
    cpreset
    wcel
    cX
    cB
    wcel
    cX
    cX
    c.le
    wbr
    cK
    posprs
    cB
    cK
    c.le
    cX
    posi.b
    posi.l
    prsref
    sylan
end
