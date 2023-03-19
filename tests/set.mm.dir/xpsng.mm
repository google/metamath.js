include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "cop.mm"
include "wceq.mm"
include "fconstg.mm"
include "adantl.mm"
include "fsng.mm"
include "mpbid.mm"

theorem xpsng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( { A } X. { B } ) = { <. A , B >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cA
    csn
    #
    cB
    csn
    #
    @2
    @3
    cxp
    #
    wf
    #
    @4
    cA
    cB
    cop
    csn
    wceq
    @1
    @5
    @0
    @2
    cB
    cW
    fconstg
    adantl
    cA
    cB
    cV
    cW
    @4
    fsng
    mpbid
end
