include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "ccnv.mm"
include "cfv.mm"
include "wb.mm"
include "snssi.mm"
include "funimass3.mm"
include "sylan2.mm"
include "fvex.mm"
include "snss.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "df-fn.mm"
include "biimpri.mm"
include "mpan2.mm"
include "fnsnfv.mm"
include "sylan.mm"
include "sseq1d.mm"
include "syl5bb.mm"
include "snssg.mm"
include "adantl.mm"
include "3bitr4d.mm"

theorem fvimacnvALT
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A e. dom F ) -> ( ( F ` A ) e. B <-> A e. ( `' F " B ) ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    wa
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
    @4
    cF
    ccnv
    cB
    cima
    #
    wss
    #
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    cA
    @7
    wcel
    #
    @2
    @0
    @4
    @1
    wss
    @6
    @8
    wb
    cA
    @1
    snssi
    @4
    cB
    cF
    funimass3
    sylan2
    @10
    @9
    csn
    #
    cB
    wss
    @3
    @6
    @9
    cB
    cA
    cF
    fvex
    snss
    @3
    @12
    @5
    cB
    @0
    cF
    @1
    wfn
    #
    @2
    @12
    @5
    wceq
    @0
    @1
    @1
    wceq
    #
    @13
    @1
    eqid
    @13
    @0
    @14
    wa
    cF
    @1
    df-fn
    biimpri
    mpan2
    @1
    cA
    cF
    fnsnfv
    sylan
    sseq1d
    syl5bb
    @2
    @11
    @8
    wb
    @0
    cA
    @7
    @1
    snssg
    adantl
    3bitr4d
end
