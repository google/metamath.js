include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wsbc.mm"
include "snidg.mm"
include "csb.mm"
include "sbcel2.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "csbvarg.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "bitri.mm"
include "sylibr.mm"
include "spesbcd.mm"

theorem bj-sels
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> E. x A e. x )

  proof
    cA
    cV
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cA
    csn
    #
    @0
    cA
    @3
    wcel
    #
    @2
    vx
    @3
    wsbc
    #
    cA
    cV
    snidg
    @5
    cA
    vx
    @3
    @1
    csb
    #
    wcel
    @4
    vx
    @3
    cA
    @1
    sbcel2
    @6
    @3
    cA
    @3
    cvv
    wcel
    @6
    @3
    wceq
    cA
    snex
    vx
    @3
    cvv
    csbvarg
    ax-mp
    eleq2i
    bitri
    sylibr
    spesbcd
end
