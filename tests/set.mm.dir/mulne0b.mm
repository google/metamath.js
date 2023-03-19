include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "mul0or.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6rbbr.mm"

theorem mulne0b
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A =/= 0 /\ B =/= 0 ) <-> ( A x. B ) =/= 0 ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cA
    cB
    cmul
    co
    #
    cc0
    wne
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wo
    #
    wn
    cA
    cc0
    wne
    cB
    cc0
    wne
    wa
    @0
    @2
    @1
    cc0
    cA
    cB
    mul0or
    necon3abid
    cA
    cc0
    cB
    cc0
    neanior
    syl6rbbr
end
