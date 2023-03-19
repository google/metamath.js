include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "cxp.mm"
include "wfn.mm"
include "fnpm.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"
include "elpm2g.mm"
include "syl.mm"
include "ibi.mm"

theorem elpmi
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F e. ( A ^pm B ) -> ( F : dom F --> A /\ dom F C_ B ) )

  proof
    cF
    cA
    cB
    cpm
    co
    #
    wcel
    #
    cF
    cdm
    #
    cA
    cF
    wf
    @2
    cB
    wss
    wa
    #
    @1
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    @1
    @3
    wb
    @1
    @0
    c0
    wceq
    @4
    @0
    cF
    n0i
    cA
    cB
    cvv
    cpm
    cpm
    cvv
    cvv
    cxp
    #
    wfn
    cpm
    cdm
    @5
    wceq
    fnpm
    @5
    cpm
    fndm
    ax-mp
    ndmov
    nsyl2
    cA
    cB
    cF
    cvv
    cvv
    elpm2g
    syl
    ibi
end
