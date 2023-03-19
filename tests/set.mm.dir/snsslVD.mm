include "csn.mm"
include "wss.mm"
include "wcel.mm"
include "idn1.mm"
include "snid.mm"
include "ssel2.mm"
include "e10an.mm"
include "in1.mm"

theorem snsslVD
  let cA: class A
  let cB: class B
  assume snsslVD.1: |- A e. _V


  assert |- ( { A } C_ B -> A e. B )

  proof
    cA
    csn
    #
    cB
    wss
    #
    cA
    cB
    wcel
    #
    @1
    @1
    cA
    @0
    wcel
    @2
    @1
    idn1
    cA
    snsslVD.1
    snid
    @0
    cB
    cA
    ssel2
    e10an
    in1
end
