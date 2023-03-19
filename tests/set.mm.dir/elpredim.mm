include "cpred.mm"
include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wbr.mm"
include "df-pred.mm"
include "elin2.mm"
include "cop.mm"
include "cvv.mm"
include "wb.mm"
include "wa.mm"
include "elimasng.mm"
include "opelcnvg.mm"
include "bitrd.mm"
include "mpan.mm"
include "ibi.mm"
include "df-br.mm"
include "sylibr.mm"
include "simplbiim.mm"

theorem elpredim
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  assume elpredim.1: |- X e. _V


  assert |- ( Y e. Pred ( R , A , X ) -> Y R X )

  proof
    cY
    cA
    cR
    cX
    cpred
    #
    wcel
    cY
    cA
    wcel
    cY
    cR
    ccnv
    #
    cX
    csn
    cima
    #
    wcel
    #
    cY
    cX
    cR
    wbr
    #
    cY
    cA
    @2
    @0
    cA
    cR
    cX
    df-pred
    elin2
    @3
    cY
    cX
    cop
    cR
    wcel
    #
    @4
    @3
    @5
    cX
    cvv
    wcel
    #
    @3
    @3
    @5
    wb
    elpredim.1
    @6
    @3
    wa
    @3
    cX
    cY
    cop
    @1
    wcel
    @5
    @1
    cX
    cY
    cvv
    @2
    elimasng
    cX
    cY
    cvv
    @2
    cR
    opelcnvg
    bitrd
    mpan
    ibi
    cY
    cX
    cR
    df-br
    sylibr
    simplbiim
end
