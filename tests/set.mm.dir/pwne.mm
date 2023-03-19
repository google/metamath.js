include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wn.mm"
include "wne.mm"
include "pwnss.mm"
include "eqimss.mm"
include "necon3bi.mm"
include "syl.mm"

theorem pwne
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ~P A =/= A )

  proof
    cA
    cV
    wcel
    cA
    cpw
    #
    cA
    wss
    #
    wn
    @0
    cA
    wne
    cA
    cV
    pwnss
    @1
    @0
    cA
    @0
    cA
    eqimss
    necon3bi
    syl
end
