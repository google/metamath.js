include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "neanior.mm"
include "elpri.mm"
include "con3i.mm"
include "sylbi.mm"
include "mp2an.mm"

theorem nelpri
  let cA: class A
  let cB: class B
  let cC: class C
  assume nelpri.1: |- A =/= B
  assume nelpri.2: |- A =/= C


  assert |- -. A e. { B , C }

  proof
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cA
    cB
    cC
    cpr
    wcel
    #
    wn
    #
    nelpri.1
    nelpri.2
    @0
    @1
    wa
    cA
    cB
    wceq
    cA
    cC
    wceq
    wo
    #
    wn
    @3
    cA
    cB
    cA
    cC
    neanior
    @2
    @4
    cA
    cB
    cC
    elpri
    con3i
    sylbi
    mp2an
end
