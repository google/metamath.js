include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "ccm.mm"
include "wbr.mm"
include "wi.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "sseq1.mm"
include "breq1.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "breq2.mm"
include "h0elch.mm"
include "elimel.mm"
include "lecmi.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem lecm
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ B ) -> A C_H B )

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
    wss
    #
    cA
    cB
    ccm
    wbr
    #
    @0
    @1
    @2
    @3
    wi
    @0
    cA
    c0h
    cif
    #
    cB
    wss
    #
    @4
    cB
    ccm
    wbr
    #
    wi
    @4
    @1
    cB
    c0h
    cif
    #
    wss
    #
    @4
    @7
    ccm
    wbr
    #
    wi
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
    sseq1
    cA
    @4
    cB
    ccm
    breq1
    imbi12d
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
    sseq2
    cB
    @7
    @4
    ccm
    breq2
    imbi12d
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
    lecmi
    dedth2h
    3impia
end
