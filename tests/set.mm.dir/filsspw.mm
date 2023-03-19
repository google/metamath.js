include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "cpw.mm"
include "wss.mm"
include "filfbas.mm"
include "fbsspw.mm"
include "syl.mm"

theorem filsspw
  let cF: class F
  let cX: class X


  assert |- ( F e. ( Fil ` X ) -> F C_ ~P X )

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
    cX
    cpw
    wss
    cF
    cX
    filfbas
    cX
    cF
    fbsspw
    syl
end
