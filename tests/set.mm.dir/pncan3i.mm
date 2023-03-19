include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "pncan3.mm"
include "mp2an.mm"

theorem pncan3i
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( A + ( B - A ) ) = B

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cA
    cmin
    co
    caddc
    co
    cB
    wceq
    negidi.1
    pncan3i.2
    cA
    cB
    pncan3
    mp2an
end
