include "cmul.mm"
include "co.mm"
include "mulcomi.mm"
include "eqtri.mm"

theorem mulcomli
  let cA: class A
  let cB: class B
  let cC: class C
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC
  assume mulcomli.3: |- ( A x. B ) = C


  assert |- ( B x. A ) = C

  proof
    cB
    cA
    cmul
    co
    cA
    cB
    cmul
    co
    cC
    cB
    cA
    axi.2
    axi.1
    mulcomi
    mulcomli.3
    eqtri
end
