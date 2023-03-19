include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cdif.mm"
include "wa.mm"
include "cun.mm"
include "unfi.mm"
include "undif1.mm"
include "eleq1i.mm"
include "unfir.mm"
include "simpld.mm"
include "sylbi.mm"
include "syl.mm"
include "expcom.mm"
include "con3d.mm"
include "impcom.mm"

theorem difinf
  let cA: class A
  let cB: class B


  assert |- ( ( -. A e. Fin /\ B e. Fin ) -> -. ( A \ B ) e. Fin )

  proof
    cB
    cfn
    wcel
    #
    cA
    cfn
    wcel
    #
    wn
    cA
    cB
    cdif
    #
    cfn
    wcel
    #
    wn
    @0
    @3
    @1
    @3
    @0
    @1
    @3
    @0
    wa
    @2
    cB
    cun
    #
    cfn
    wcel
    #
    @1
    @2
    cB
    unfi
    @5
    cA
    cB
    cun
    #
    cfn
    wcel
    #
    @1
    @4
    @6
    cfn
    cA
    cB
    undif1
    eleq1i
    @7
    @1
    @0
    cA
    cB
    unfir
    simpld
    sylbi
    syl
    expcom
    con3d
    impcom
end
