include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wfal.mm"
include "fal.mm"
include "eqneqall.mm"
include "imp.mm"
include "mto.mm"

theorem nonconne
  let cA: class A
  let cB: class B


  assert |- -. ( A = B /\ A =/= B )

  proof
    cA
    cB
    wceq
    #
    cA
    cB
    wne
    #
    wa
    wfal
    fal
    @0
    @1
    wfal
    wfal
    cA
    cB
    eqneqall
    imp
    mto
end
