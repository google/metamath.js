include "chj.mm"
include "co.mm"
include "chjcli.mm"
include "chub2i.mm"
include "lecmii.mm"

theorem cmj2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- B C_H ( A vH B )

  proof
    cB
    cA
    cB
    chj
    co
    pjoml2.2
    cA
    cB
    pjoml2.1
    pjoml2.2
    chjcli
    cB
    cA
    pjoml2.2
    pjoml2.1
    chub2i
    lecmii
end
