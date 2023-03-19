include "cpred.mm"
include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wa.mm"
include "wbr.mm"
include "df-pred.mm"
include "elin2.mm"
include "eliniseg.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem elpred
  let cA: class A
  let cD: class D
  let cR: class R
  let cX: class X
  let cY: class Y
  assume elpred.1: |- Y e. _V


  assert |- ( X e. D -> ( Y e. Pred ( R , A , X ) <-> ( Y e. A /\ Y R X ) ) )

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
    #
    cY
    cR
    ccnv
    cX
    csn
    cima
    #
    wcel
    #
    wa
    cX
    cD
    wcel
    #
    @1
    cY
    cX
    cR
    wbr
    #
    wa
    cY
    cA
    @2
    @0
    cA
    cR
    cX
    df-pred
    elin2
    @4
    @3
    @5
    @1
    cR
    cX
    cY
    cD
    elpred.1
    eliniseg
    anbi2d
    syl5bb
end
