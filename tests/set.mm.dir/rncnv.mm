include "cdm.mm"
include "ccnv.mm"
include "crn.mm"
include "dfdm4.mm"
include "eqcomi.mm"

theorem rncnv
  let cA: class A


  assert |- ran `' A = dom A

  proof
    cA
    cdm
    cA
    ccnv
    crn
    cA
    dfdm4
    eqcomi
end
