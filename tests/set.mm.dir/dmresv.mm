include "cvv.mm"
include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "dmres.mm"
include "incom.mm"
include "inv1.mm"
include "3eqtri.mm"

theorem dmresv
  let cA: class A


  assert |- dom ( A |` _V ) = dom A

  proof
    cA
    cvv
    cres
    cdm
    cvv
    cA
    cdm
    #
    cin
    @0
    cvv
    cin
    @0
    cA
    cvv
    dmres
    cvv
    @0
    incom
    @0
    inv1
    3eqtri
end
