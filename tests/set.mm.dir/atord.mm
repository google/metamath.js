include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "ccm.mm"
include "wbr.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "sseq2.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "atordi.mm"
include "dedth.mm"
include "3impib.mm"

theorem atord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. HAtoms /\ A C_H B ) -> ( B C_ A \/ B C_ ( _|_ ` A ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    cA
    cB
    ccm
    wbr
    #
    cB
    cA
    wss
    #
    cB
    cA
    cort
    cfv
    #
    wss
    #
    wo
    #
    @0
    @1
    @2
    wa
    #
    @6
    wi
    @1
    @0
    cA
    c0h
    cif
    #
    cB
    ccm
    wbr
    #
    wa
    #
    cB
    @8
    wss
    #
    cB
    @8
    cort
    cfv
    #
    wss
    #
    wo
    #
    wi
    cA
    c0h
    cA
    @8
    wceq
    #
    @7
    @10
    @6
    @14
    @15
    @2
    @9
    @1
    cA
    @8
    cB
    ccm
    breq1
    anbi2d
    @15
    @3
    @11
    @5
    @13
    cA
    @8
    cB
    sseq2
    @15
    @4
    @12
    cB
    cA
    @8
    cort
    fveq2
    sseq2d
    orbi12d
    imbi12d
    @8
    cB
    cA
    c0h
    cch
    h0elch
    elimel
    atordi
    dedth
    3impib
end
