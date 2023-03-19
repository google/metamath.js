include "cima.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "cin.mm"
include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "imadisj.mm"
include "incom.mm"
include "fndm.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "syl5bb.mm"

theorem fnimaeq0
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ B C_ A ) -> ( ( F " B ) = (/) <-> B = (/) ) )

  proof
    cF
    cB
    cima
    c0
    wceq
    cF
    cdm
    #
    cB
    cin
    #
    c0
    wceq
    cF
    cA
    wfn
    #
    cB
    cA
    wss
    #
    wa
    #
    cB
    c0
    wceq
    cF
    cB
    imadisj
    @4
    @1
    cB
    c0
    @4
    @1
    cB
    @0
    cin
    #
    cB
    @0
    cB
    incom
    @4
    cB
    @0
    wss
    #
    @5
    cB
    wceq
    @2
    @6
    @3
    @2
    @0
    cA
    cB
    cA
    cF
    fndm
    sseq2d
    biimpar
    cB
    @0
    df-ss
    sylib
    syl5eq
    eqeq1d
    syl5bb
end
