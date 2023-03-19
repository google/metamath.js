include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvadd12.mm"
include "syl3an3.mm"
include "wa.mm"
include "hvsubval.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "3adant2.mm"
include "3eqtr4d.mm"

theorem hvaddsub12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( A +h ( B -h C ) ) = ( B +h ( A -h C ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    cA
    cB
    c1
    cneg
    #
    cC
    csm
    co
    #
    cva
    co
    #
    cva
    co
    #
    cB
    cA
    @4
    cva
    co
    #
    cva
    co
    #
    cA
    cB
    cC
    cmv
    co
    #
    cva
    co
    #
    cB
    cA
    cC
    cmv
    co
    #
    cva
    co
    #
    @2
    @0
    @1
    @4
    chil
    wcel
    #
    @6
    @8
    wceq
    @3
    cc
    wcel
    @2
    @13
    neg1cn
    @3
    cC
    hvmulcl
    mpan
    cA
    cB
    @4
    hvadd12
    syl3an3
    @1
    @2
    @10
    @6
    wceq
    @0
    @1
    @2
    wa
    @9
    @5
    cA
    cva
    cB
    cC
    hvsubval
    oveq2d
    3adant1
    @0
    @2
    @12
    @8
    wceq
    @1
    @0
    @2
    wa
    @11
    @7
    cB
    cva
    cA
    cC
    hvsubval
    oveq2d
    3adant2
    3eqtr4d
end
