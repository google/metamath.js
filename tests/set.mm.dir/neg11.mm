include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "wceq.mm"
include "negeq.mm"
include "negneg.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "impbid1.mm"

theorem neg11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( -u A = -u B <-> A = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cneg
    #
    cB
    cneg
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @5
    @3
    cneg
    #
    @4
    cneg
    #
    wceq
    @2
    @6
    @3
    @4
    negeq
    @0
    @1
    @7
    cA
    @8
    cB
    cA
    negneg
    cB
    negneg
    eqeqan12d
    syl5ib
    cA
    cB
    negeq
    impbid1
end
