include "cgz.mm"
include "wcel.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cz.mm"
include "cim.mm"
include "elgz.mm"
include "simp1bi.mm"

theorem gzcn
  let cA: class A


  assert |- ( A e. Z[i] -> A e. CC )

  proof
    cA
    cgz
    wcel
    cA
    cc
    wcel
    cA
    cre
    cfv
    cz
    wcel
    cA
    cim
    cfv
    cz
    wcel
    cA
    elgz
    simp1bi
end
