include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "addsubassi.mm"
include "eqtri.mm"

theorem assraddsubi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x
  assume assraddsubi.1: |- B e. CC
  assume assraddsubi.2: |- C e. CC
  assume assraddsubi.3: |- D e. CC
  assume assraddsubi.4: |- A = ( ( B + C ) - D )


  assert |- A = ( B + ( C - D ) )

  proof
    cA
    cB
    cC
    caddc
    co
    cD
    cmin
    co
    cB
    cC
    cD
    cmin
    co
    caddc
    co
    assraddsubi.4
    cB
    cC
    cD
    assraddsubi.1
    assraddsubi.2
    assraddsubi.3
    addsubassi
    eqtri
end
