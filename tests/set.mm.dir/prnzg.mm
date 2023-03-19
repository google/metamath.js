include "wcel.mm"
include "cpr.mm"
include "c0.mm"
include "wne.mm"
include "prid1g.mm"
include "ne0i.mm"
include "syl.mm"

theorem prnzg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> { A , B } =/= (/) )

  proof
    cA
    cV
    wcel
    cA
    cA
    cB
    cpr
    #
    wcel
    @0
    c0
    wne
    cA
    cB
    cV
    prid1g
    @0
    cA
    ne0i
    syl
end
