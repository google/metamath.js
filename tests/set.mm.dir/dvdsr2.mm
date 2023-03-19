include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "dvdsr.mm"
include "baib.mm"

theorem dvdsr2
  let vz: setvar z
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let cZ: class Z
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )
  assume dvdsr.3: |- .x. = ( .r ` R )

  disjoint B z
  disjoint X z
  disjoint Y z
  disjoint R z
  disjoint .x. z
  disjoint x y
  disjoint .|| x
  disjoint .|| y
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint .x. r
  disjoint .x. x
  disjoint .x. y
  assert |- ( X e. B -> ( X .|| Y <-> E. z e. B ( z .x. X ) = Y ) )

  proof
    cX
    cY
    c.pa
    wbr
    cX
    cB
    wcel
    vz
    cv
    cX
    c.x
    co
    cY
    wceq
    vz
    cB
    wrex
    vz
    cB
    c.pa
    cR
    c.x
    cX
    cY
    dvdsr.1
    dvdsr.2
    dvdsr.3
    dvdsr
    baib
end
