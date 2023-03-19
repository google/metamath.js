include "cv.mm"
include "cfv.mm"
include "co.mm"
include "oveq1.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "dvrfval.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem dvrval
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume dvrval.b: |- B = ( Base ` R )
  assume dvrval.t: |- .x. = ( .r ` R )
  assume dvrval.u: |- U = ( Unit ` R )
  assume dvrval.i: |- I = ( invr ` R )
  assume dvrval.d: |- ./ = ( /r ` R )


  assert |- ( ( X e. B /\ Y e. U ) -> ( X ./ Y ) = ( X .x. ( I ` Y ) ) )

  proof
    vx
    vy
    cX
    cY
    cB
    cU
    vx
    cv
    #
    vy
    cv
    #
    cI
    cfv
    #
    c.x
    co
    cX
    cY
    cI
    cfv
    #
    c.x
    co
    c.dv
    cX
    @2
    c.x
    co
    @0
    cX
    @2
    c.x
    oveq1
    @1
    cY
    wceq
    @2
    @3
    cX
    c.x
    @1
    cY
    cI
    fveq2
    oveq2d
    vx
    vy
    cB
    c.dv
    cR
    c.x
    cU
    cI
    dvrval.b
    dvrval.t
    dvrval.u
    dvrval.i
    dvrval.d
    dvrfval
    cX
    @3
    c.x
    ovex
    ovmpt2
end
