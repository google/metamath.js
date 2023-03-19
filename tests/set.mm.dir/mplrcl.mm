include "cmpl.mm"
include "reldmmpl.mm"
include "strov2rcl.mm"

theorem mplrcl
  let cB: class B
  let cP: class P
  let cR: class R
  let cI: class I
  let cX: class X
  assume mplrcl.p: |- P = ( I mPoly R )
  assume mplrcl.b: |- B = ( Base ` P )


  assert |- ( X e. B -> I e. _V )

  proof
    cB
    cR
    cP
    cmpl
    cI
    cX
    mplrcl.p
    mplrcl.b
    reldmmpl
    strov2rcl
end
