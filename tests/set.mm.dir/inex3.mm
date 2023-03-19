include "wcel.mm"
include "cin.mm"
include "cvv.mm"
include "inex1g.mm"
include "inex2ALTV.mm"
include "jaoi.mm"

theorem inex3
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V \/ B e. W ) -> ( A i^i B ) e. _V )

  proof
    cA
    cV
    wcel
    cA
    cB
    cin
    cvv
    wcel
    cB
    cW
    wcel
    cA
    cB
    cV
    inex1g
    cB
    cA
    cW
    inex2ALTV
    jaoi
end
