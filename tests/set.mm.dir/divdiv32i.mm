include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "divdiv23zi.mm"
include "mp2an.mm"

theorem divdiv32i
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divmul.4: |- B =/= 0
  assume divdiv23.5: |- C =/= 0


  assert |- ( ( A / B ) / C ) = ( ( A / C ) / B )

  proof
    cB
    cc0
    wne
    cC
    cc0
    wne
    cA
    cB
    cdiv
    co
    cC
    cdiv
    co
    cA
    cC
    cdiv
    co
    cB
    cdiv
    co
    wceq
    divmul.4
    divdiv23.5
    cA
    cB
    cC
    divclz.1
    divclz.2
    divmulz.3
    divdiv23zi
    mp2an
end
