include "wrel.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "relimasn.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wi.mm"
include "wb.mm"
include "brrelex2.mm"
include "ex.mm"
include "breq2.mm"
include "elab3g.mm"
include "syl.mm"
include "bitrd.mm"

theorem elrelimasn
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( Rel R -> ( B e. ( R " { A } ) <-> A R B ) )

  proof
    cR
    wrel
    #
    cB
    cR
    cA
    csn
    cima
    #
    wcel
    cB
    cA
    vx
    cv
    #
    cR
    wbr
    #
    vx
    cab
    #
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    @0
    @1
    @4
    cB
    vx
    cA
    cR
    relimasn
    eleq2d
    @0
    @6
    cB
    cvv
    wcel
    #
    wi
    @5
    @6
    wb
    @0
    @6
    @7
    cA
    cB
    cR
    brrelex2
    ex
    @3
    @6
    vx
    cB
    cvv
    @2
    cB
    cA
    cR
    breq2
    elab3g
    syl
    bitrd
end
