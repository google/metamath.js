include "cdiv.mm"
include "co.mm"
include "divcli.mm"
include "divcan2i.mm"
include "mulcomli.mm"

theorem divcan1i
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divcl.3: |- B =/= 0


  assert |- ( ( A / B ) x. B ) = A

  proof
    cB
    cA
    cB
    cdiv
    co
    cA
    divclz.2
    cA
    cB
    divclz.1
    divclz.2
    divcl.3
    divcli
    cA
    cB
    divclz.1
    divclz.2
    divcl.3
    divcan2i
    mulcomli
end
