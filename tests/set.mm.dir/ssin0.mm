include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "ss2in.mm"
include "3adant1.mm"
include "eqimss.mm"
include "3ad2ant1.mm"
include "sstrd.mm"
include "ss0.mm"
include "syl.mm"

theorem ssin0
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A i^i B ) = (/) /\ C C_ A /\ D C_ B ) -> ( C i^i D ) = (/) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cC
    cA
    wss
    #
    cD
    cB
    wss
    #
    w3a
    #
    cC
    cD
    cin
    #
    c0
    wss
    @5
    c0
    wceq
    @4
    @5
    @0
    c0
    @2
    @3
    @5
    @0
    wss
    @1
    cC
    cA
    cD
    cB
    ss2in
    3adant1
    @1
    @2
    @0
    c0
    wss
    @3
    @0
    c0
    eqimss
    3ad2ant1
    sstrd
    @5
    ss0
    syl
end
