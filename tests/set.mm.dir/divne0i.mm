include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "divne0.mm"
include "mp4an.mm"

theorem divne0i
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divneq0.3: |- A =/= 0
  assume divneq0.4: |- B =/= 0


  assert |- ( A / B ) =/= 0

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cc0
    wne
    divclz.1
    divneq0.3
    divclz.2
    divneq0.4
    cA
    cB
    divne0
    mp4an
end
