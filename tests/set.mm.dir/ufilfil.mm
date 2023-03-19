include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "cv.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "isufil.mm"
include "simplbi.mm"

theorem ufilfil
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( F e. ( UFil ` X ) -> F e. ( Fil ` X ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    cF
    cX
    cfil
    cfv
    wcel
    vx
    cv
    #
    cF
    wcel
    cX
    @0
    cdif
    cF
    wcel
    wo
    vx
    cX
    cpw
    wral
    vx
    cF
    cX
    isufil
    simplbi
end
