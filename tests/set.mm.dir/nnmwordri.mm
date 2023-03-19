include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "comu.mm"
include "co.mm"
include "nnmwordi.mm"
include "wceq.mm"
include "nnmcom.mm"
include "3adant2.mm"
include "3adant1.mm"
include "sseq12d.mm"
include "sylibrd.mm"

theorem nnmwordri
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( A C_ B -> ( A .o C ) C_ ( B .o C ) ) )

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
    cA
    cB
    wss
    cC
    cA
    comu
    co
    #
    cC
    cB
    comu
    co
    #
    wss
    cA
    cC
    comu
    co
    #
    cB
    cC
    comu
    co
    #
    wss
    cA
    cB
    cC
    nnmwordi
    @3
    @6
    @4
    @7
    @5
    @0
    @2
    @6
    @4
    wceq
    @1
    cA
    cC
    nnmcom
    3adant2
    @1
    @2
    @7
    @5
    wceq
    @0
    cB
    cC
    nnmcom
    3adant1
    sseq12d
    sylibrd
end
