include "cfne.mm"
include "wbr.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "fnetg.mm"
include "sselda.mm"
include "tg2.mm"
include "stoic3.mm"

theorem fnessex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S

  disjoint A x
  disjoint B x
  disjoint P x
  disjoint S x
  assert |- ( ( A Fne B /\ S e. A /\ P e. S ) -> E. x e. B ( P e. x /\ x C_ S ) )

  proof
    cA
    cB
    cfne
    wbr
    #
    cS
    cA
    wcel
    cS
    cB
    ctg
    cfv
    #
    wcel
    cP
    cS
    wcel
    cP
    vx
    cv
    #
    wcel
    @2
    cS
    wss
    wa
    vx
    cB
    wrex
    @0
    cA
    @1
    cS
    cA
    cB
    fnetg
    sselda
    vx
    cS
    cB
    cP
    tg2
    stoic3
end
