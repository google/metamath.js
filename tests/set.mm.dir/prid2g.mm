include "wcel.mm"
include "cpr.mm"
include "prid1g.mm"
include "prcom.mm"
include "syl6eleq.mm"

theorem prid2g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> B e. { A , B } )

  proof
    cB
    cV
    wcel
    cB
    cB
    cA
    cpr
    cA
    cB
    cpr
    cB
    cA
    cV
    prid1g
    cB
    cA
    prcom
    syl6eleq
end
