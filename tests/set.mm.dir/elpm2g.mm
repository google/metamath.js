include "wcel.mm"
include "wa.mm"
include "cpm.mm"
include "co.mm"
include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "cdm.mm"
include "wf.mm"
include "elpmg.mm"
include "funssxp.mm"
include "syl6bb.mm"

theorem elpm2g
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( F e. ( A ^pm B ) <-> ( F : dom F --> A /\ dom F C_ B ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cF
    cA
    cB
    cpm
    co
    wcel
    cF
    wfun
    cF
    cB
    cA
    cxp
    wss
    wa
    cF
    cdm
    #
    cA
    cF
    wf
    @0
    cB
    wss
    wa
    cA
    cB
    cF
    cV
    cW
    elpmg
    cB
    cA
    cF
    funssxp
    syl6bb
end
