include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "ax-hvcom.mm"
include "mp2an.mm"

theorem hvcomi
  let cA: class A
  let cB: class B
  assume hvaddcl.1: |- A e. ~H
  assume hvaddcl.2: |- B e. ~H


  assert |- ( A +h B ) = ( B +h A )

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
    cB
    cA
    cva
    co
    wceq
    hvaddcl.1
    hvaddcl.2
    cA
    cB
    ax-hvcom
    mp2an
end
