include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "3anrot.mm"
include "nnmword.mm"
include "sylanb.mm"
include "3anrev.mm"
include "anbi12d.mm"
include "bicomd.mm"
include "eqss.mm"
include "3bitr4g.mm"

theorem nnmcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. _om /\ B e. _om /\ C e. _om ) /\ (/) e. A ) -> ( ( A .o B ) = ( A .o C ) <-> B = C ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    w3a
    #
    c0
    cA
    wcel
    #
    wa
    #
    cA
    cB
    comu
    co
    #
    cA
    cC
    comu
    co
    #
    wss
    #
    @7
    @6
    wss
    #
    wa
    #
    cB
    cC
    wss
    #
    cC
    cB
    wss
    #
    wa
    #
    @6
    @7
    wceq
    cB
    cC
    wceq
    @5
    @13
    @10
    @5
    @11
    @8
    @12
    @9
    @3
    @1
    @2
    @0
    w3a
    @4
    @11
    @8
    wb
    @0
    @1
    @2
    3anrot
    cB
    cC
    cA
    nnmword
    sylanb
    @3
    @2
    @1
    @0
    w3a
    @4
    @12
    @9
    wb
    @0
    @1
    @2
    3anrev
    cC
    cB
    cA
    nnmword
    sylanb
    anbi12d
    bicomd
    @6
    @7
    eqss
    cB
    cC
    eqss
    3bitr4g
end
