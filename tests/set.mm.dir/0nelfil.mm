include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "c0.mm"
include "wn.mm"
include "filfbas.mm"
include "0nelfb.mm"
include "syl.mm"

theorem 0nelfil
  let cF: class F
  let cX: class X


  assert |- ( F e. ( Fil ` X ) -> -. (/) e. F )

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
    c0
    cF
    wcel
    wn
    cF
    cX
    filfbas
    cX
    cF
    0nelfb
    syl
end
