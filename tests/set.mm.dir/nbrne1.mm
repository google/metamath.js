include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "breq2.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem nbrne1
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( A R B /\ -. A R C ) -> B =/= C )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cC
    cR
    wbr
    #
    wn
    cB
    cC
    wne
    @0
    @1
    cB
    cC
    cB
    cC
    wceq
    @0
    @1
    cB
    cC
    cA
    cR
    breq2
    biimpcd
    necon3bd
    imp
end
