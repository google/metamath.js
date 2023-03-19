include "cid.mm"
include "wfun.mm"
include "wcel.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "funi.mm"
include "ididg.mm"
include "funbrfv.mm"
include "mpsyl.mm"

theorem fvi
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( _I ` A ) = A )

  proof
    cid
    wfun
    cA
    cV
    wcel
    cA
    cA
    cid
    wbr
    cA
    cid
    cfv
    cA
    wceq
    funi
    cA
    cV
    ididg
    cA
    cA
    cid
    funbrfv
    mpsyl
end
