include "cxp.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "df-br.mm"
include "opelxp.mm"
include "bitri.mm"

theorem brxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( A ( C X. D ) B <-> ( A e. C /\ B e. D ) )

  proof
    cA
    cB
    cC
    cD
    cxp
    #
    wbr
    cA
    cB
    cop
    @0
    wcel
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cA
    cB
    @0
    df-br
    cA
    cB
    cC
    cD
    opelxp
    bitri
end
