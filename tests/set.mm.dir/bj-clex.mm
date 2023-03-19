include "wcel.mm"
include "cima.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "cab.mm"
include "imaexg.mm"
include "bj-snsetex.mm"
include "syl.mm"

theorem bj-clex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> { x | { x } e. ( A " B ) } e. _V )

  proof
    cA
    cV
    wcel
    cA
    cB
    cima
    #
    cvv
    wcel
    vx
    cv
    csn
    @0
    wcel
    vx
    cab
    cvv
    wcel
    cA
    cB
    cV
    imaexg
    vx
    @0
    cvv
    bj-snsetex
    syl
end
