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
include "divmul2.mm"
include "mulcom.mm"
include "adantrr.mm"
include "3adant1.mm"
include "eqeq2d.mm"
include "bitr4d.mm"

theorem divmul3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / C ) = B <-> A = ( B x. C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cA
    cC
    cdiv
    co
    cB
    wceq
    cA
    cC
    cB
    cmul
    co
    #
    wceq
    cA
    cB
    cC
    cmul
    co
    #
    wceq
    cA
    cB
    cC
    divmul2
    @5
    @7
    @6
    cA
    @1
    @4
    @7
    @6
    wceq
    #
    @0
    @1
    @2
    @8
    @3
    cB
    cC
    mulcom
    adantrr
    3adant1
    eqeq2d
    bitr4d
end
