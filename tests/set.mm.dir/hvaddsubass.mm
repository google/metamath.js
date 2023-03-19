include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cmv.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "ax-hvass.mm"
include "syl3an3.mm"
include "hvaddcl.mm"
include "hvsubval.mm"
include "stoic3.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem hvaddsubass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A +h B ) -h C ) = ( A +h ( B -h C ) ) )

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
    #
    cA
    cB
    cva
    co
    #
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
    cA
    cB
    @6
    cva
    co
    #
    cva
    co
    #
    @4
    cC
    cmv
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
    @2
    @0
    @1
    @6
    chil
    wcel
    #
    @7
    @9
    wceq
    @5
    cc
    wcel
    @2
    @12
    neg1cn
    @5
    cC
    hvmulcl
    mpan
    cA
    cB
    @6
    ax-hvass
    syl3an3
    @0
    @1
    @4
    chil
    wcel
    @2
    @10
    @7
    wceq
    cA
    cB
    hvaddcl
    @4
    cC
    hvsubval
    stoic3
    @3
    @11
    @8
    cA
    cva
    @1
    @2
    @11
    @8
    wceq
    @0
    cB
    cC
    hvsubval
    3adant1
    oveq2d
    3eqtr4d
end
