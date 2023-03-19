include "wfun.mm"
include "ccnv.mm"
include "cima.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "wss.mm"
include "snssi.mm"
include "funimass2.mm"
include "sylan2.mm"
include "fvex.mm"
include "snss.mm"
include "cdm.mm"
include "wceq.mm"
include "cnvimass.mm"
include "sseli.mm"
include "wfn.mm"
include "funfn.mm"
include "fnsnfv.mm"
include "sylanb.mm"
include "sseq1d.mm"
include "syl5bb.mm"
include "mpbird.mm"

theorem fvimacnvi
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A e. ( `' F " B ) ) -> ( F ` A ) e. B )

  proof
    cF
    wfun
    #
    cA
    cF
    ccnv
    cB
    cima
    #
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    cF
    cA
    csn
    #
    cima
    #
    cB
    wss
    #
    @2
    @0
    @6
    @1
    wss
    @8
    cA
    @1
    snssi
    @6
    cB
    cF
    funimass2
    sylan2
    @5
    @4
    csn
    #
    cB
    wss
    @3
    @8
    @4
    cB
    cA
    cF
    fvex
    snss
    @3
    @9
    @7
    cB
    @2
    @0
    cA
    cF
    cdm
    #
    wcel
    #
    @9
    @7
    wceq
    #
    @1
    @10
    cA
    cF
    cB
    cnvimass
    sseli
    @0
    cF
    @10
    wfn
    @11
    @12
    cF
    funfn
    @10
    cA
    cF
    fnsnfv
    sylanb
    sylan2
    sseq1d
    syl5bb
    mpbird
end
