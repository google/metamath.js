include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "hvaddcl.mm"
include "mp2an.mm"

theorem hvaddcli
  let cA: class A
  let cB: class B
  assume hvaddcl.1: |- A e. ~H
  assume hvaddcl.2: |- B e. ~H


  assert |- ( A +h B ) e. ~H

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    cA
    cB
    cva
    co
    chil
    wcel
    hvaddcl.1
    hvaddcl.2
    cA
    cB
    hvaddcl
    mp2an
end
