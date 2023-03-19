include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "wa.mm"
include "onelon.mm"
include "alephord2.mm"
include "biimpd.mm"
include "expimpd.mm"
include "mpcom.mm"
include "ex.mm"

theorem alephord2i
  let cA: class A
  let cB: class B


  assert |- ( B e. On -> ( A e. B -> ( aleph ` A ) e. ( aleph ` B ) ) )

  proof
    cB
    con0
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cale
    cfv
    cB
    cale
    cfv
    wcel
    #
    cA
    con0
    wcel
    #
    @0
    @1
    wa
    @2
    cB
    cA
    onelon
    @3
    @0
    @1
    @2
    @3
    @0
    wa
    @1
    @2
    cA
    cB
    alephord2
    biimpd
    expimpd
    mpcom
    ex
end
