include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cdm.mm"
include "df-br.mm"
include "opeldm.mm"
include "sylbi.mm"

theorem breldm
  let cA: class A
  let cB: class B
  let cR: class R
  let vy: setvar y
  let cC: class C
  assume opeldm.1: |- A e. _V
  assume opeldm.2: |- B e. _V


  assert |- ( A R B -> A e. dom R )

  proof
    cA
    cB
    cR
    wbr
    cA
    cB
    cop
    cR
    wcel
    cA
    cR
    cdm
    wcel
    cA
    cB
    cR
    df-br
    cA
    cB
    cR
    opeldm.1
    opeldm.2
    opeldm
    sylbi
end
