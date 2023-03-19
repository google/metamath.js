include "chil.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cr.mm"
include "wral.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "mp2.mm"

theorem lnophmlem1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnophmlem.1: |- A e. ~H
  assume lnophmlem.2: |- B e. ~H
  assume lnophmlem.3: |- T e. LinOp
  assume lnophmlem.4: |- A. x e. ~H ( x .ih ( T ` x ) ) e. RR

  disjoint A x
  disjoint B x
  disjoint T x
  assert |- ( A .ih ( T ` A ) ) e. RR

  proof
    cA
    chil
    wcel
    vx
    cv
    #
    @0
    cT
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    vx
    chil
    wral
    cA
    cA
    cT
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    lnophmlem.1
    lnophmlem.4
    @3
    @6
    vx
    cA
    chil
    @0
    cA
    wceq
    #
    @2
    @5
    cr
    @7
    @0
    cA
    @1
    @4
    csp
    @7
    id
    @0
    cA
    cT
    fveq2
    oveq12d
    eleq1d
    rspcv
    mp2
end
