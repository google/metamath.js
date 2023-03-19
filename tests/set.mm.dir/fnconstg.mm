include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "fconstg.mm"
include "ffn.mm"
include "syl.mm"

theorem fnconstg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( A X. { B } ) Fn A )

  proof
    cB
    cV
    wcel
    cA
    cB
    csn
    #
    cA
    @0
    cxp
    #
    wf
    @1
    cA
    wfn
    cA
    cB
    cV
    fconstg
    cA
    @0
    @1
    ffn
    syl
end
