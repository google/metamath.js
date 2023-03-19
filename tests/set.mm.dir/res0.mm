include "c0.mm"
include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "0xp.mm"
include "ineq2i.mm"
include "in0.mm"
include "3eqtri.mm"

theorem res0
  let cA: class A


  assert |- ( A |` (/) ) = (/)

  proof
    cA
    c0
    cres
    cA
    c0
    cvv
    cxp
    #
    cin
    cA
    c0
    cin
    c0
    cA
    c0
    df-res
    @0
    c0
    cA
    cvv
    0xp
    ineq2i
    cA
    in0
    3eqtri
end
