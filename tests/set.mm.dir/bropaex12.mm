include "wbr.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "df-br.mm"
include "eleq2i.mm"
include "bitri.mm"
include "elopaelxp.mm"
include "sylbi.mm"
include "opelxp.mm"
include "sylib.mm"

theorem bropaex12
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume bropaex12.1: |- R = { <. x , y >. | ps }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( A R B -> ( A e. _V /\ B e. _V ) )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cop
    #
    cvv
    cvv
    cxp
    wcel
    #
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    @0
    @1
    wps
    vx
    vy
    copab
    #
    wcel
    #
    @2
    @0
    @1
    cR
    wcel
    @4
    cA
    cB
    cR
    df-br
    cR
    @3
    @1
    bropaex12.1
    eleq2i
    bitri
    wps
    vx
    vy
    @1
    elopaelxp
    sylbi
    cA
    cB
    cvv
    cvv
    opelxp
    sylib
end
