include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wpss.mm"
include "wb.mm"
include "choccl.mm"
include "chpsscon3.mm"
include "sylan.mm"
include "wceq.mm"
include "ococ.mm"
include "adantr.mm"
include "psseq2d.mm"
include "bitrd.mm"

theorem chpsscon1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( ( _|_ ` A ) C. B <-> ( _|_ ` B ) C. A ) )

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
    cort
    cfv
    #
    cB
    wpss
    #
    cB
    cort
    cfv
    #
    @3
    cort
    cfv
    #
    wpss
    #
    @5
    cA
    wpss
    @0
    @3
    cch
    wcel
    @1
    @4
    @7
    wb
    cA
    choccl
    @3
    cB
    chpsscon3
    sylan
    @2
    @6
    cA
    @5
    @0
    @6
    cA
    wceq
    @1
    cA
    ococ
    adantr
    psseq2d
    bitrd
end
