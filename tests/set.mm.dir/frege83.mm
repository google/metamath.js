include "wcel.mm"
include "cun.mm"
include "wi.mm"
include "whe.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "frege36.mm"
include "wo.mm"
include "elun.mm"
include "df-or.mm"
include "bitri.mm"
include "sylibr.mm"
include "cvv.mm"
include "elexi.mm"
include "unex.mm"
include "frege82.mm"
include "ax-mp.mm"

theorem frege83
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege83.x: |- X e. S
  assume frege83.y: |- Y e. T
  assume frege83.r: |- R e. U
  assume frege83.b: |- B e. V
  assume frege83.c: |- C e. W


  assert |- ( R hereditary ( B u. C ) -> ( X e. B -> ( X ( t+ ` R ) Y -> Y e. ( B u. C ) ) ) )

  proof
    cX
    cB
    wcel
    #
    cX
    cB
    cC
    cun
    #
    wcel
    #
    wi
    @1
    cR
    whe
    @0
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    cY
    @1
    wcel
    wi
    wi
    wi
    @0
    @0
    wn
    cX
    cC
    wcel
    #
    wi
    #
    @2
    @0
    @3
    frege36
    @2
    @0
    @3
    wo
    @4
    cX
    cB
    cC
    elun
    @0
    @3
    df-or
    bitri
    sylibr
    @0
    @1
    cvv
    cR
    cS
    cT
    cU
    cX
    cY
    frege83.x
    frege83.y
    frege83.r
    cB
    cC
    cB
    cV
    frege83.b
    elexi
    cC
    cW
    frege83.c
    elexi
    unex
    frege82
    ax-mp
end
