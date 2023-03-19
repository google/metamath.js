include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cmpt.mm"
include "cxp.mm"
include "cop.mm"
include "fconstmpt.mm"
include "xpsng.mm"
include "syl5reqr.mm"

theorem fmptsn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  assert |- ( ( A e. V /\ B e. W ) -> { <. A , B >. } = ( x e. { A } |-> B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    vx
    cA
    csn
    #
    cB
    cmpt
    @0
    cB
    csn
    cxp
    cA
    cB
    cop
    csn
    vx
    @0
    cB
    fconstmpt
    cA
    cB
    cV
    cW
    xpsng
    syl5reqr
end
