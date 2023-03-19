include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "wceq.mm"
include "mapvalg.mm"
include "mp2an.mm"

theorem mapval
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume mapval.1: |- A e. _V
  assume mapval.2: |- B e. _V

  disjoint A f
  disjoint B f
  assert |- ( A ^m B ) = { f | f : B --> A }

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cmap
    co
    cB
    cA
    vf
    cv
    wf
    vf
    cab
    wceq
    mapval.1
    mapval.2
    cA
    cB
    cvv
    cvv
    vf
    mapvalg
    mp2an
end
