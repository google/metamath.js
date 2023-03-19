include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "subcl.mm"
include "mp2an.mm"

theorem subcli
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( A - B ) e. CC

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
    cc
    wcel
    negidi.1
    pncan3i.2
    cA
    cB
    subcl
    mp2an
end
