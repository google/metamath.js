include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "dmres.mm"
include "inss2.mm"
include "eqsstri.mm"

theorem dmresss
  let cA: class A
  let cB: class B


  assert |- dom ( A |` B ) C_ dom A

  proof
    cA
    cB
    cres
    cdm
    cB
    cA
    cdm
    #
    cin
    @0
    cA
    cB
    dmres
    cB
    @0
    inss2
    eqsstri
end
