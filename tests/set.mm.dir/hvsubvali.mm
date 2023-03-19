include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "wceq.mm"
include "hvsubval.mm"
include "mp2an.mm"

theorem hvsubvali
  let cA: class A
  let cB: class B
  assume hvaddcl.1: |- A e. ~H
  assume hvaddcl.2: |- B e. ~H


  assert |- ( A -h B ) = ( A +h ( -u 1 .h B ) )

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    cA
    cB
    cmv
    co
    cA
    c1
    cneg
    cB
    csm
    co
    cva
    co
    wceq
    hvaddcl.1
    hvaddcl.2
    cA
    cB
    hvsubval
    mp2an
end
