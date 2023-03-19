include "copab.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "df-br.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "opprc.mm"
include "0neqopab.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "syl.mm"
include "con4i.mm"
include "sylbi.mm"

theorem brabv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y


  assert |- ( X { <. x , y >. | ph } Y -> ( X e. _V /\ Y e. _V ) )

  proof
    cX
    cY
    wph
    vx
    vy
    copab
    #
    wbr
    cX
    cY
    cop
    #
    @0
    wcel
    #
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    wa
    #
    cX
    cY
    @0
    df-br
    @3
    @2
    @3
    wn
    @1
    c0
    wceq
    #
    @2
    wn
    cX
    cY
    opprc
    @4
    @2
    c0
    @0
    wcel
    wph
    vx
    vy
    0neqopab
    @1
    c0
    @0
    eleq1
    mtbiri
    syl
    con4i
    sylbi
end
