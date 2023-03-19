include "c0.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "res0.mm"
include "rneqi.mm"
include "rn0.mm"
include "3eqtri.mm"

theorem ima0
  let cA: class A


  assert |- ( A " (/) ) = (/)

  proof
    cA
    c0
    cima
    cA
    c0
    cres
    #
    crn
    c0
    crn
    c0
    cA
    c0
    df-ima
    @0
    c0
    cA
    res0
    rneqi
    rn0
    3eqtri
end
