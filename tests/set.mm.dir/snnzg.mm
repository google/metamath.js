include "wcel.mm"
include "csn.mm"
include "c0.mm"
include "wne.mm"
include "snidg.mm"
include "ne0i.mm"
include "syl.mm"

theorem snnzg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> { A } =/= (/) )

  proof
    cA
    cV
    wcel
    cA
    cA
    csn
    #
    wcel
    @0
    c0
    wne
    cA
    cV
    snidg
    @0
    cA
    ne0i
    syl
end
