include "csn.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "fconstfv.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "fnfun.mm"
include "fndm.mm"
include "eqimss2.mm"
include "syl.mm"
include "funconstss.mm"
include "syl2anc.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem fconst3
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( F : A --> { B } <-> ( F Fn A /\ A C_ ( `' F " { B } ) ) )

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
    vx
    cv
    cF
    cfv
    cB
    wceq
    vx
    cA
    wral
    #
    wa
    @1
    cA
    cF
    ccnv
    @0
    cima
    wss
    #
    wa
    vx
    cA
    cB
    cF
    fconstfv
    @1
    @2
    @3
    @1
    cF
    wfun
    cA
    cF
    cdm
    #
    wss
    #
    @2
    @3
    wb
    cA
    cF
    fnfun
    @1
    @4
    cA
    wceq
    @5
    cA
    cF
    fndm
    cA
    @4
    eqimss2
    syl
    vx
    cA
    cB
    cF
    funconstss
    syl2anc
    pm5.32i
    bitri
end
