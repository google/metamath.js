include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "isfil.mm"
include "simplbi.mm"

theorem filfbas
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( F e. ( Fil ` X ) -> F e. ( fBas ` X ) )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    cF
    cX
    cfbas
    cfv
    wcel
    cF
    vx
    cv
    #
    cpw
    cin
    c0
    wne
    @0
    cF
    wcel
    wi
    vx
    cX
    cpw
    wral
    vx
    cF
    cX
    isfil
    simplbi
end
