include "wcel.mm"
include "cep.mm"
include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "df-pred.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "relimasn.mm"
include "ax-mp.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "brcnvg.mm"
include "mpan2.mm"
include "epelg.mm"
include "bitrd.mm"
include "abbi1dv.mm"
include "syl5eq.mm"
include "ineq2d.mm"

theorem predep
  let cA: class A
  let cB: class B
  let cX: class X
  let vy: setvar y


  assert |- ( X e. B -> Pred ( _E , A , X ) = ( A i^i X ) )

  proof
    cX
    cB
    wcel
    #
    cA
    cep
    cX
    cpred
    cA
    cep
    ccnv
    #
    cX
    csn
    cima
    #
    cin
    cA
    cX
    cin
    cA
    cep
    cX
    df-pred
    @0
    @2
    cX
    cA
    @0
    @2
    cX
    vy
    cv
    #
    @1
    wbr
    #
    vy
    cab
    #
    cX
    @1
    wrel
    @2
    @5
    wceq
    cep
    relcnv
    vy
    cX
    @1
    relimasn
    ax-mp
    @0
    @4
    vy
    cX
    @0
    @4
    @3
    cX
    cep
    wbr
    #
    @3
    cX
    wcel
    @0
    @3
    cvv
    wcel
    @4
    @6
    wb
    vy
    vex
    cX
    @3
    cB
    cvv
    cep
    brcnvg
    mpan2
    @3
    cX
    cB
    epelg
    bitrd
    abbi1dv
    syl5eq
    ineq2d
    syl5eq
end
