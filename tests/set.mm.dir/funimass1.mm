include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wfun.mm"
include "crn.mm"
include "wa.mm"
include "imass2.mm"
include "cin.mm"
include "funimacnv.mm"
include "wceq.mm"
include "dfss.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "sseq1d.mm"
include "syl5ib.mm"

theorem funimass1
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A C_ ran F ) -> ( ( `' F " A ) C_ B -> A C_ ( F " B ) ) )

  proof
    cF
    ccnv
    cA
    cima
    #
    cB
    wss
    cF
    @0
    cima
    #
    cF
    cB
    cima
    #
    wss
    cF
    wfun
    #
    cA
    cF
    crn
    #
    wss
    #
    wa
    #
    cA
    @2
    wss
    @0
    cB
    cF
    imass2
    @6
    @1
    cA
    @2
    @3
    @5
    @1
    cA
    @4
    cin
    #
    cA
    cA
    cF
    funimacnv
    @5
    cA
    @7
    @5
    cA
    @7
    wceq
    cA
    @4
    dfss
    biimpi
    eqcomd
    sylan9eq
    sseq1d
    syl5ib
end
