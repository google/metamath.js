include "wf.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wrel.mm"
include "wss.mm"
include "frel.mm"
include "relssdmrn.mm"
include "syl.mm"
include "wceq.mm"
include "fdm.mm"
include "eqimss.mm"
include "frn.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sstrd.mm"

theorem fssxp
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> F C_ ( A X. B ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cF
    cdm
    #
    cF
    crn
    #
    cxp
    #
    cA
    cB
    cxp
    #
    @0
    cF
    wrel
    cF
    @3
    wss
    cA
    cB
    cF
    frel
    cF
    relssdmrn
    syl
    @0
    @1
    cA
    wss
    #
    @2
    cB
    wss
    @3
    @4
    wss
    @0
    @1
    cA
    wceq
    @5
    cA
    cB
    cF
    fdm
    @1
    cA
    eqimss
    syl
    cA
    cB
    cF
    frn
    @1
    cA
    @2
    cB
    xpss12
    syl2anc
    sstrd
end
