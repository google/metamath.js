include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "filtop.mm"
include "ne0i.mm"
include "syl.mm"

theorem filn0
  let cF: class F
  let cX: class X


  assert |- ( F e. ( Fil ` X ) -> F =/= (/) )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    cX
    cF
    wcel
    cF
    c0
    wne
    cF
    cX
    filtop
    cF
    cX
    ne0i
    syl
end
