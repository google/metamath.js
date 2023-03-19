include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "wb.mm"
include "cmcm3.mm"
include "ancoms.mm"
include "cmcm.mm"
include "choccl.mm"
include "sylan2.mm"
include "3bitr4d.mm"

theorem cmcm2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_H B <-> A C_H ( _|_ ` B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    cB
    cA
    ccm
    wbr
    #
    cB
    cort
    cfv
    #
    cA
    ccm
    wbr
    #
    cA
    cB
    ccm
    wbr
    cA
    @3
    ccm
    wbr
    #
    @1
    @0
    @2
    @4
    wb
    cB
    cA
    cmcm3
    ancoms
    cA
    cB
    cmcm
    @1
    @0
    @3
    cch
    wcel
    @5
    @4
    wb
    cB
    choccl
    cA
    @3
    cmcm
    sylan2
    3bitr4d
end
