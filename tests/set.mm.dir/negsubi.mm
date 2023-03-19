include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "negsub.mm"
include "mp2an.mm"

theorem negsubi
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- ( A + -u B ) = ( A - B )

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
    caddc
    co
    cA
    cB
    cmin
    co
    wceq
    negidi.1
    pncan3i.2
    cA
    cB
    negsub
    mp2an
end
