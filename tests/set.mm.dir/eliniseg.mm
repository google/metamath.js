include "wcel.mm"
include "cvv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "cop.mm"
include "elimasng.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "brcnvg.mm"
include "bitrd.mm"
include "mpan2.mm"

theorem eliniseg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume eliniseg.1: |- C e. _V


  assert |- ( B e. V -> ( C e. ( `' A " { B } ) <-> C A B ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cvv
    wcel
    #
    cC
    cA
    ccnv
    #
    cB
    csn
    cima
    wcel
    #
    cC
    cB
    cA
    wbr
    #
    wb
    eliniseg.1
    @0
    @1
    wa
    #
    @3
    cB
    cC
    @2
    wbr
    #
    @4
    @5
    @3
    cB
    cC
    cop
    @2
    wcel
    @6
    @2
    cB
    cC
    cV
    cvv
    elimasng
    cB
    cC
    @2
    df-br
    syl6bbr
    cB
    cC
    cV
    cvv
    cA
    brcnvg
    bitrd
    mpan2
end
