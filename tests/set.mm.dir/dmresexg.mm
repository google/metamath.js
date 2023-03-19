include "wcel.mm"
include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "cvv.mm"
include "dmres.mm"
include "inex1g.mm"
include "syl5eqel.mm"

theorem dmresexg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> dom ( A |` B ) e. _V )

  proof
    cB
    cV
    wcel
    cA
    cB
    cres
    cdm
    cB
    cA
    cdm
    #
    cin
    cvv
    cA
    cB
    dmres
    cB
    @0
    cV
    inex1g
    syl5eqel
end
