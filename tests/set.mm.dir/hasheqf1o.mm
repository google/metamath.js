include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "hashen.mm"
include "bren.mm"
include "syl6bb.mm"

theorem hasheqf1o
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint A f
  disjoint B f
  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( ( # ` A ) = ( # ` B ) <-> E. f f : A -1-1-onto-> B ) )

  proof
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    wa
    cA
    chash
    cfv
    cB
    chash
    cfv
    wceq
    cA
    cB
    cen
    wbr
    cA
    cB
    vf
    cv
    wf1o
    vf
    wex
    cA
    cB
    hashen
    cA
    cB
    vf
    bren
    syl6bb
end
