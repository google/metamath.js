include "wcel.mm"
include "cvv.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wceq.mm"
include "elex.mm"
include "wrex.mm"
include "dfima2.mm"
include "breq1.mm"
include "rexsng.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "syl.mm"

theorem imasng
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x

  disjoint A y
  disjoint R y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( A e. B -> ( R " { A } ) = { y | A R y } )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    #
    cR
    cA
    csn
    #
    cima
    #
    cA
    vy
    cv
    #
    cR
    wbr
    #
    vy
    cab
    #
    wceq
    cA
    cB
    elex
    @0
    @2
    vx
    cv
    #
    @3
    cR
    wbr
    #
    vx
    @1
    wrex
    #
    vy
    cab
    @5
    vx
    vy
    cR
    @1
    dfima2
    @0
    @8
    @4
    vy
    @7
    @4
    vx
    cA
    cvv
    @6
    cA
    @3
    cR
    breq1
    rexsng
    abbidv
    syl5eq
    syl
end
