include "cba.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"

theorem hlex
  let cU: class U
  let cX: class X
  assume hlex.1: |- X = ( BaseSet ` U )


  assert |- X e. _V

  proof
    cX
    cU
    cba
    cfv
    cvv
    hlex.1
    cU
    cba
    fvex
    eqeltri
end
