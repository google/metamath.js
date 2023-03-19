include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "pncan.mm"
include "mp2an.mm"

theorem pncan3oi
  let cA: class A
  let cB: class B
  assume pncan3oi.1: |- A e. CC
  assume pncan3oi.2: |- B e. CC


  assert |- ( ( A + B ) - B ) = A

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cB
    cmin
    co
    cA
    wceq
    pncan3oi.1
    pncan3oi.2
    cA
    cB
    pncan
    mp2an
end
