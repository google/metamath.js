include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wb.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "sseq1.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "bibi12d.mm"
include "sseq2.mm"
include "sseq1d.mm"
include "ifchhv.mm"
include "chsscon3i.mm"
include "dedth2h.mm"

theorem chsscon3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_ B <-> ( _|_ ` B ) C_ ( _|_ ` A ) ) )

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
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wss
    #
    wb
    @0
    cA
    chil
    cif
    #
    cB
    wss
    #
    @3
    @6
    cort
    cfv
    #
    wss
    #
    wb
    @6
    @1
    cB
    chil
    cif
    #
    wss
    #
    @10
    cort
    cfv
    #
    @8
    wss
    #
    wb
    cA
    cB
    chil
    chil
    cA
    @6
    wceq
    #
    @2
    @7
    @5
    @9
    cA
    @6
    cB
    sseq1
    @14
    @4
    @8
    @3
    cA
    @6
    cort
    fveq2
    sseq2d
    bibi12d
    cB
    @10
    wceq
    #
    @7
    @11
    @9
    @13
    cB
    @10
    @6
    sseq2
    @15
    @3
    @12
    @8
    cB
    @10
    cort
    fveq2
    sseq1d
    bibi12d
    @6
    @10
    cA
    ifchhv
    cB
    ifchhv
    chsscon3i
    dedth2h
end
