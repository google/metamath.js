include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "hashneq0.mm"
include "biimpa.mm"

theorem hashgt0n0
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ 0 < ( # ` A ) ) -> A =/= (/) )

  proof
    cA
    cV
    wcel
    cc0
    cA
    chash
    cfv
    clt
    wbr
    cA
    c0
    wne
    cA
    cV
    hashneq0
    biimpa
end
