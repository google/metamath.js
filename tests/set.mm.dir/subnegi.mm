include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subneg.mm"
include "mp2an.mm"

theorem subnegi
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( A - -u B ) = ( A + B )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cneg
    cmin
    co
    cA
    cB
    caddc
    co
    wceq
    negidi.1
    pncan3i.2
    cA
    cB
    subneg
    mp2an
end
