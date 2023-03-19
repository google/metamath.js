include "csn.mm"
include "wf.mm"
include "wfn.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "fconst3.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "biantrurd.mm"
include "eqss.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem fconst4
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> { B } <-> ( F Fn A /\ ( `' F " { B } ) = A ) )

  proof
    cA
    cB
    csn
    #
    cF
    wf
    cF
    cA
    wfn
    #
    cA
    cF
    ccnv
    @0
    cima
    #
    wss
    #
    wa
    @1
    @2
    cA
    wceq
    #
    wa
    cA
    cB
    cF
    fconst3
    @1
    @3
    @4
    @1
    @3
    @2
    cA
    wss
    #
    @3
    wa
    @4
    @1
    @5
    @3
    @1
    cF
    cdm
    @2
    cA
    cF
    @0
    cnvimass
    cA
    cF
    fndm
    syl5sseq
    biantrurd
    @2
    cA
    eqss
    syl6bbr
    pm5.32i
    bitri
end
