include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wb.mm"
include "choccl.mm"
include "chsscon3.mm"
include "sylan.mm"
include "wceq.mm"
include "ococ.mm"
include "adantr.mm"
include "sseq2d.mm"
include "bitrd.mm"

theorem chsscon1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( ( _|_ ` A ) C_ B <-> ( _|_ ` B ) C_ A ) )

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
    wss
    #
    cB
    cort
    cfv
    #
    @3
    cort
    cfv
    #
    wss
    #
    @5
    cA
    wss
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
    chsscon3
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
    sseq2d
    bitrd
end
