include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wcel.mm"
include "cort.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "spansni.mm"
include "eleq2i.mm"
include "h1de2ci.mm"
include "bitri.mm"

theorem elspansni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  assume spansn.1: |- A e. ~H

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( B e. ( span ` { A } ) <-> E. x e. CC B = ( x .h A ) )

  proof
    cB
    cA
    csn
    #
    cspn
    cfv
    #
    wcel
    cB
    @0
    cort
    cfv
    cort
    cfv
    #
    wcel
    cB
    vx
    cv
    cA
    csm
    co
    wceq
    vx
    cc
    wrex
    @1
    @2
    cB
    cA
    spansn.1
    spansni
    eleq2i
    vx
    cB
    cA
    spansn.1
    h1de2ci
    bitri
end
