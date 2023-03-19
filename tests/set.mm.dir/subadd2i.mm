include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "wb.mm"
include "subadd2.mm"
include "mp3an.mm"

theorem subadd2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC
  assume subadd.3: |- C e. CC


  assert |- ( ( A - B ) = C <-> ( C + B ) = A )

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
    cC
    cB
    caddc
    co
    cA
    wceq
    wb
    negidi.1
    pncan3i.2
    subadd.3
    cA
    cB
    cC
    subadd2
    mp3an
end
