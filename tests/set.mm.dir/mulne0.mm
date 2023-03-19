include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "mulne0b.mm"
include "biimpa.mm"
include "an4s.mm"

theorem mulne0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( A x. B ) =/= 0 )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    cA
    cB
    cmul
    co
    cc0
    wne
    #
    @0
    @1
    wa
    @2
    @3
    wa
    @4
    cA
    cB
    mulne0b
    biimpa
    an4s
end
