include "cv.mm"
include "cfv.mm"
include "fveq2.mm"
include "staffval.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem stafval
  let cA: class A
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.as: class .*
  let vx: setvar x
  let vf: setvar f
  assume staffval.b: |- B = ( Base ` R )
  assume staffval.i: |- .* = ( *r ` R )
  assume staffval.f: |- .xb = ( *rf ` R )


  assert |- ( A e. B -> ( .xb ` A ) = ( .* ` A ) )

  proof
    vx
    cA
    vx
    cv
    #
    c.as
    cfv
    cA
    c.as
    cfv
    cB
    c.xb
    @0
    cA
    c.as
    fveq2
    vx
    cB
    cR
    c.xb
    c.as
    staffval.b
    staffval.i
    staffval.f
    staffval
    cA
    c.as
    fvex
    fvmpt
end
