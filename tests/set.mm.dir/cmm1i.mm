include "cin.mm"
include "chincli.mm"
include "inss1.mm"
include "lecmii.mm"
include "cmcmii.mm"

theorem cmm1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- A C_H ( A i^i B )

  proof
    cA
    cB
    cin
    #
    cA
    cA
    cB
    pjoml2.1
    pjoml2.2
    chincli
    #
    pjoml2.1
    @0
    cA
    @1
    pjoml2.1
    cA
    cB
    inss1
    lecmii
    cmcmii
end
