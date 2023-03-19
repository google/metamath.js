include "wrel.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "releldm.mm"
include "mpan.mm"

theorem releldmi
  let cA: class A
  let cB: class B
  let cR: class R
  assume releldm.1: |- Rel R


  assert |- ( A R B -> A e. dom R )

  proof
    cR
    wrel
    cA
    cB
    cR
    wbr
    cA
    cR
    cdm
    wcel
    releldm.1
    cA
    cB
    cR
    releldm
    mpan
end
