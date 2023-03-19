include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "df-pss.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dfpss2
  let cA: class A
  let cB: class B


  assert |- ( A C. B <-> ( A C_ B /\ -. A = B ) )

  proof
    cA
    cB
    wpss
    cA
    cB
    wss
    #
    cA
    cB
    wne
    #
    wa
    @0
    cA
    cB
    wceq
    wn
    #
    wa
    cA
    cB
    df-pss
    @1
    @2
    @0
    cA
    cB
    df-ne
    anbi2i
    bitri
end
