include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wpss.mm"
include "wn.mm"
include "wa.mm"
include "pm4.61.mm"
include "dfpss2.mm"
include "bitr4i.mm"
include "con1bii.mm"

theorem npss
  let cA: class A
  let cB: class B


  assert |- ( -. A C. B <-> ( A C_ B -> A = B ) )

  proof
    cA
    cB
    wss
    #
    cA
    cB
    wceq
    #
    wi
    #
    cA
    cB
    wpss
    #
    @2
    wn
    @0
    @1
    wn
    wa
    @3
    @0
    @1
    pm4.61
    cA
    cB
    dfpss2
    bitr4i
    con1bii
end
