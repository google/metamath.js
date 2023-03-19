include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "negdi.mm"
include "mp2an.mm"

theorem negdii
  let cA: class A
  let cB: class B
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC


  assert |- -u ( A + B ) = ( -u A + -u B )

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
    cneg
    cA
    cneg
    cB
    cneg
    caddc
    co
    wceq
    negidi.1
    pncan3i.2
    cA
    cB
    negdi
    mp2an
end
