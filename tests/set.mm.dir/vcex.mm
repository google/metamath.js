include "cop.mm"
include "cvc.mm"
include "wcel.mm"
include "wbr.mm"
include "cvv.mm"
include "wa.mm"
include "df-br.mm"
include "wrel.mm"
include "cxp.mm"
include "wss.mm"
include "vcrel.mm"
include "df-rel.mm"
include "mpbi.mm"
include "brel.mm"
include "sylbir.mm"

theorem vcex
  let cS: class S
  let cG: class G


  assert |- ( <. G , S >. e. CVecOLD -> ( G e. _V /\ S e. _V ) )

  proof
    cG
    cS
    cop
    cvc
    wcel
    cG
    cS
    cvc
    wbr
    cG
    cvv
    wcel
    cS
    cvv
    wcel
    wa
    cG
    cS
    cvc
    df-br
    cG
    cS
    cvv
    cvv
    cvc
    cvc
    wrel
    cvc
    cvv
    cvv
    cxp
    wss
    vcrel
    cvc
    df-rel
    mpbi
    brel
    sylbir
end
