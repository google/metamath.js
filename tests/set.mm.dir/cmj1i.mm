include "chj.mm"
include "co.mm"
include "chjcli.mm"
include "chub1i.mm"
include "lecmii.mm"

theorem cmj1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- A C_H ( A vH B )

  proof
    cA
    cA
    cB
    chj
    co
    pjoml2.1
    cA
    cB
    pjoml2.1
    pjoml2.2
    chjcli
    cA
    cB
    pjoml2.1
    pjoml2.2
    chub1i
    lecmii
end
