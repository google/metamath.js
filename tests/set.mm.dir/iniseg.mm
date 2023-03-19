include "wcel.mm"
include "cvv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wceq.mm"
include "elex.mm"
include "vex.mm"
include "eliniseg.mm"
include "abbi2dv.mm"
include "syl.mm"

theorem iniseg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( B e. V -> ( `' A " { B } ) = { x | x A B } )

  proof
    cB
    cV
    wcel
    cB
    cvv
    wcel
    #
    cA
    ccnv
    cB
    csn
    cima
    #
    vx
    cv
    #
    cB
    cA
    wbr
    #
    vx
    cab
    wceq
    cB
    cV
    elex
    @0
    @3
    vx
    @1
    cA
    cB
    @2
    cvv
    vx
    vex
    eliniseg
    abbi2dv
    syl
end
