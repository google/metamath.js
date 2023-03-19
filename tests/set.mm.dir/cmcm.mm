include "cch.mm"
include "wcel.mm"
include "ccm.mm"
include "wbr.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "breq1.mm"
include "breq2.mm"
include "bibi12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "cmcmi.mm"
include "dedth2h.mm"

theorem cmcm
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_H B <-> B C_H A ) )

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
    cB
    cA
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
    cB
    @4
    ccm
    wbr
    #
    wb
    @4
    @1
    cB
    c0h
    cif
    #
    ccm
    wbr
    #
    @7
    @4
    ccm
    wbr
    #
    wb
    cA
    cB
    c0h
    c0h
    cA
    @4
    wceq
    @2
    @5
    @3
    @6
    cA
    @4
    cB
    ccm
    breq1
    cA
    @4
    cB
    ccm
    breq2
    bibi12d
    cB
    @7
    wceq
    @5
    @8
    @6
    @9
    cB
    @7
    @4
    ccm
    breq2
    cB
    @7
    @4
    ccm
    breq1
    bibi12d
    @4
    @7
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
    cmcmi
    dedth2h
end
