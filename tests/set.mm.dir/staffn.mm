include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "dffn5.mm"
include "biimpi.mm"
include "staffval.mm"
include "syl6reqr.mm"

theorem staffn
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.as: class .*
  let cA: class A
  let vx: setvar x
  let vf: setvar f
  assume staffval.b: |- B = ( Base ` R )
  assume staffval.i: |- .* = ( *r ` R )
  assume staffval.f: |- .xb = ( *rf ` R )


  assert |- ( .* Fn B -> .xb = .* )

  proof
    c.as
    cB
    wfn
    #
    c.as
    vx
    cB
    vx
    cv
    c.as
    cfv
    cmpt
    #
    c.xb
    @0
    c.as
    @1
    wceq
    vx
    cB
    c.as
    dffn5
    biimpi
    vx
    cB
    cR
    c.xb
    c.as
    staffval.b
    staffval.i
    staffval.f
    staffval
    syl6reqr
end
