include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "hvmulcl.mm"
include "mp2an.mm"

theorem hvmulcli
  let cA: class A
  let cB: class B
  assume hvmulcl.1: |- A e. CC
  assume hvmulcl.2: |- B e. ~H


  assert |- ( A .h B ) e. ~H

  proof
    cA
    cc
    wcel
    cB
    chil
    wcel
    cA
    cB
    csm
    co
    chil
    wcel
    hvmulcl.1
    hvmulcl.2
    cA
    cB
    hvmulcl
    mp2an
end
