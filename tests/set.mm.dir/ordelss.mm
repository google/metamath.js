include "word.mm"
include "wtr.mm"
include "wcel.mm"
include "wss.mm"
include "ordtr.mm"
include "trss.mm"
include "imp.mm"
include "sylan.mm"

theorem ordelss
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ B e. A ) -> B C_ A )

  proof
    cA
    word
    cA
    wtr
    #
    cB
    cA
    wcel
    #
    cB
    cA
    wss
    #
    cA
    ordtr
    @0
    @1
    @2
    cA
    cB
    trss
    imp
    sylan
end
