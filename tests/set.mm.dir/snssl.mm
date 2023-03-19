include "csn.mm"
include "wss.mm"
include "wcel.mm"
include "snid.mm"
include "ssel2.mm"
include "mpan2.mm"

theorem snssl
  let cA: class A
  let cB: class B
  assume snssl.1: |- A e. _V


  assert |- ( { A } C_ B -> A e. B )

  proof
    cA
    csn
    #
    cB
    wss
    cA
    @0
    wcel
    cA
    cB
    wcel
    cA
    snssl.1
    snid
    @0
    cB
    cA
    ssel2
    mpan2
end
