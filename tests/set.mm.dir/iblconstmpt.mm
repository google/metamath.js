include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "cc.mm"
include "w3a.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cibl.mm"
include "fconstmpt.mm"
include "iblconst.mm"
include "syl5eqelr.mm"

theorem iblconstmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ( A e. dom vol /\ ( vol ` A ) e. RR /\ B e. CC ) -> ( x e. A |-> B ) e. L^1 )

  proof
    cA
    cvol
    cdm
    wcel
    cA
    cvol
    cfv
    cr
    wcel
    cB
    cc
    wcel
    w3a
    vx
    cA
    cB
    cmpt
    cA
    cB
    csn
    cxp
    cibl
    vx
    cA
    cB
    fconstmpt
    cA
    cB
    iblconst
    syl5eqelr
end
