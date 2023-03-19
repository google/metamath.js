include "wcel.mm"
include "wa.mm"
include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wbr.mm"
include "wb.mm"
include "df-pred.mm"
include "elin2.mm"
include "baib.mm"
include "adantl.mm"
include "cop.mm"
include "elimasng.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "brcnvg.mm"
include "3bitrd.mm"

theorem elpredg
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. B /\ Y e. A ) -> ( Y e. Pred ( R , A , X ) <-> Y R X ) )

  proof
    cX
    cB
    wcel
    #
    cY
    cA
    wcel
    #
    wa
    #
    cY
    cA
    cR
    cX
    cpred
    #
    wcel
    #
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
    cX
    cY
    @5
    wbr
    #
    cY
    cX
    cR
    wbr
    @1
    @4
    @7
    wb
    @0
    @4
    @1
    @7
    cY
    cA
    @6
    @3
    cA
    cR
    cX
    df-pred
    elin2
    baib
    adantl
    @2
    @7
    cX
    cY
    cop
    @5
    wcel
    @8
    @5
    cX
    cY
    cB
    cA
    elimasng
    cX
    cY
    @5
    df-br
    syl6bbr
    cX
    cY
    cB
    cA
    cR
    brcnvg
    3bitrd
end
