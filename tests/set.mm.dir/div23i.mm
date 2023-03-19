include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "pm3.2i.mm"
include "div23.mm"
include "mp3an.mm"

theorem div23i
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divass.4: |- C =/= 0


  assert |- ( ( A x. B ) / C ) = ( ( A / C ) x. B )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    cA
    cB
    cmul
    co
    cC
    cdiv
    co
    cA
    cC
    cdiv
    co
    cB
    cmul
    co
    wceq
    divclz.1
    divclz.2
    @0
    @1
    divmulz.3
    divass.4
    pm3.2i
    cA
    cB
    cC
    div23
    mp3an
end
