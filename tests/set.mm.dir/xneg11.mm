include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cxne.mm"
include "wceq.mm"
include "xnegeq.mm"
include "xnegneg.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "impbid1.mm"

theorem xneg11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( -e A = -e B <-> A = B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cxne
    #
    cB
    cxne
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @5
    @3
    cxne
    #
    @4
    cxne
    #
    wceq
    @2
    @6
    @3
    @4
    xnegeq
    @0
    @1
    @7
    cA
    @8
    cB
    cA
    xnegneg
    cB
    xnegneg
    eqeqan12d
    syl5ib
    cA
    cB
    xnegeq
    impbid1
end
