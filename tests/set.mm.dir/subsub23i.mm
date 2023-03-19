include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "subsub23.mm"
include "mp3an.mm"

theorem subsub23i
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC
  assume subadd.3: |- C e. CC


  assert |- ( ( A - B ) = C <-> ( A - C ) = B )

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
    cA
    cB
    cmin
    co
    cC
    wceq
    cA
    cC
    cmin
    co
    cB
    wceq
    wb
    negidi.1
    pncan3i.2
    subadd.3
    cA
    cB
    cC
    subsub23
    mp3an
end
