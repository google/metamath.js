include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "ineq1.mm"
include "oveq12d.mm"
include "sseq12d.mm"
include "ineq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "ineq2d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "h0elch.mm"
include "elimel.mm"
include "ledii.mm"
include "dedth3h.mm"

theorem ledi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( ( A i^i B ) vH ( A i^i C ) ) C_ ( A i^i ( B vH C ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    cA
    cB
    cin
    #
    cA
    cC
    cin
    #
    chj
    co
    #
    cA
    cB
    cC
    chj
    co
    #
    cin
    #
    wss
    @0
    cA
    c0h
    cif
    #
    cB
    cin
    #
    @8
    cC
    cin
    #
    chj
    co
    #
    @8
    @6
    cin
    #
    wss
    @8
    @1
    cB
    c0h
    cif
    #
    cin
    #
    @10
    chj
    co
    #
    @8
    @13
    cC
    chj
    co
    #
    cin
    #
    wss
    @14
    @8
    @2
    cC
    c0h
    cif
    #
    cin
    #
    chj
    co
    #
    @8
    @13
    @18
    chj
    co
    #
    cin
    #
    wss
    cA
    cB
    cC
    c0h
    c0h
    c0h
    cA
    @8
    wceq
    #
    @5
    @11
    @7
    @12
    @23
    @3
    @9
    @4
    @10
    chj
    cA
    @8
    cB
    ineq1
    cA
    @8
    cC
    ineq1
    oveq12d
    cA
    @8
    @6
    ineq1
    sseq12d
    cB
    @13
    wceq
    #
    @11
    @15
    @12
    @17
    @24
    @9
    @14
    @10
    chj
    cB
    @13
    @8
    ineq2
    oveq1d
    @24
    @6
    @16
    @8
    cB
    @13
    cC
    chj
    oveq1
    ineq2d
    sseq12d
    cC
    @18
    wceq
    #
    @15
    @20
    @17
    @22
    @25
    @10
    @19
    @14
    chj
    cC
    @18
    @8
    ineq2
    oveq2d
    @25
    @16
    @21
    @8
    cC
    @18
    @13
    chj
    oveq2
    ineq2d
    sseq12d
    @8
    @13
    @18
    cA
    c0h
    cch
    h0elch
    elimel
    cB
    c0h
    cch
    h0elch
    elimel
    cC
    c0h
    cch
    h0elch
    elimel
    ledii
    dedth3h
end
