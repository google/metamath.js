include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "subsq.mm"
include "mp2an.mm"

theorem subsqi
  let cA: class A
  let cB: class B
  assume binom2.1: |- A e. CC
  assume binom2.2: |- B e. CC


  assert |- ( ( A ^ 2 ) - ( B ^ 2 ) ) = ( ( A + B ) x. ( A - B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cmin
    co
    cA
    cB
    caddc
    co
    cA
    cB
    cmin
    co
    cmul
    co
    wceq
    binom2.1
    binom2.2
    cA
    cB
    subsq
    mp2an
end
