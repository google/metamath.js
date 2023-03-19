include "wrel.mm"
include "wbr.mm"
include "crn.mm"
include "wcel.mm"
include "relelrn.mm"
include "mpan.mm"

theorem relelrni
  let cA: class A
  let cB: class B
  let cR: class R
  assume releldm.1: |- Rel R


  assert |- ( A R B -> B e. ran R )

  proof
    cR
    wrel
    cA
    cB
    cR
    wbr
    cB
    cR
    crn
    wcel
    releldm.1
    cA
    cB
    cR
    relelrn
    mpan
end
