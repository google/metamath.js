include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cmv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "hvsubval.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvaddcl.mm"
include "sylan2.mm"
include "eqeltrd.mm"

theorem hvsubcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A -h B ) e. ~H )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    cA
    cB
    cmv
    co
    cA
    c1
    cneg
    #
    cB
    csm
    co
    #
    cva
    co
    #
    chil
    cA
    cB
    hvsubval
    @1
    @0
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    @2
    cc
    wcel
    @1
    @5
    neg1cn
    @2
    cB
    hvmulcl
    mpan
    cA
    @3
    hvaddcl
    sylan2
    eqeltrd
end
