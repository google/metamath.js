include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "subeq0.mm"
include "mp2an.mm"

theorem subeq0i
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( ( A - B ) = 0 <-> A = B )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmin
    co
    cc0
    wceq
    cA
    cB
    wceq
    wb
    negidi.1
    pncan3i.2
    cA
    cB
    subeq0
    mp2an
end
