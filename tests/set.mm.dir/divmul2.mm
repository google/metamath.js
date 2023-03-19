include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "divmul.mm"
include "eqcom.mm"
include "syl6bb.mm"

theorem divmul2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / C ) = B <-> A = ( C x. B ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cC
    cc0
    wne
    wa
    w3a
    cA
    cC
    cdiv
    co
    cB
    wceq
    cC
    cB
    cmul
    co
    #
    cA
    wceq
    cA
    @0
    wceq
    cA
    cB
    cC
    divmul
    @0
    cA
    eqcom
    syl6bb
end
