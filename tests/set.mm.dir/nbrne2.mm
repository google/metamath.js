include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "breq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem nbrne2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( A R C /\ -. B R C ) -> A =/= B )

  proof
    cA
    cC
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    wn
    cA
    cB
    wne
    @0
    @1
    cA
    cB
    cA
    cB
    wceq
    @0
    @1
    cA
    cB
    cC
    cR
    breq1
    biimpcd
    necon3bd
    imp
end
