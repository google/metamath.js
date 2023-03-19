include "co.mm"
include "cop.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "df-ov.mm"
include "fvssunirn.mm"
include "eqsstri.mm"

theorem ovssunirn
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( X F Y ) C_ U. ran F

  proof
    cX
    cY
    cF
    co
    cX
    cY
    cop
    #
    cF
    cfv
    cF
    crn
    cuni
    cX
    cY
    cF
    df-ov
    cF
    @0
    fvssunirn
    eqsstri
end
