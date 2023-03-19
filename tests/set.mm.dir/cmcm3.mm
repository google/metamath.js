include "cch.mm"
include "wcel.mm"
include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "h0elch.mm"
include "elimel.mm"
include "cmcm3i.mm"
include "dedth2h.mm"

theorem cmcm3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_H B <-> ( _|_ ` A ) C_H B ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    ccm
    wbr
    #
    cA
    cort
    cfv
    #
    cB
    ccm
    wbr
    #
    wb
    @0
    cA
    c0h
    cif
    #
    cB
    ccm
    wbr
    #
    @5
    cort
    cfv
    #
    cB
    ccm
    wbr
    #
    wb
    @5
    @1
    cB
    c0h
    cif
    #
    ccm
    wbr
    #
    @7
    @9
    ccm
    wbr
    #
    wb
    cA
    cB
    c0h
    c0h
    cA
    @5
    wceq
    #
    @2
    @6
    @4
    @8
    cA
    @5
    cB
    ccm
    breq1
    @12
    @3
    @7
    cB
    ccm
    cA
    @5
    cort
    fveq2
    breq1d
    bibi12d
    cB
    @9
    wceq
    @6
    @10
    @8
    @11
    cB
    @9
    @5
    ccm
    breq2
    cB
    @9
    @7
    ccm
    breq2
    bibi12d
    @5
    @9
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
    cmcm3i
    dedth2h
end
