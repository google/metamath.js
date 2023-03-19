include "chil.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cc.mm"
include "hicl.mm"
include "mp2an.mm"

theorem hicli
  let cA: class A
  let cB: class B
  assume hicl.1: |- A e. ~H
  assume hicl.2: |- B e. ~H


  assert |- ( A .ih B ) e. CC

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    cA
    cB
    csp
    co
    cc
    wcel
    hicl.1
    hicl.2
    cA
    cB
    hicl
    mp2an
end
