include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wpss.mm"
include "wb.mm"
include "choccl.mm"
include "chpsscon3.mm"
include "sylan2.mm"
include "wceq.mm"
include "ococ.mm"
include "adantl.mm"
include "psseq1d.mm"
include "bitrd.mm"

theorem chpsscon2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C. ( _|_ ` B ) <-> B C. ( _|_ ` A ) ) )

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
    #
    cA
    cB
    cort
    cfv
    #
    wpss
    #
    @3
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wpss
    #
    cB
    @6
    wpss
    @1
    @0
    @3
    cch
    wcel
    @4
    @7
    wb
    cB
    choccl
    cA
    @3
    chpsscon3
    sylan2
    @2
    @5
    cB
    @6
    @1
    @5
    cB
    wceq
    @0
    cB
    ococ
    adantl
    psseq1d
    bitrd
end
