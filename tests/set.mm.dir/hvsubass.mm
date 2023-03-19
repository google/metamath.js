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
include "hvaddsubass.mm"
include "syl3an2.mm"
include "hvsubval.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "simp1.mm"
include "hvaddcl.mm"
include "3adant1.mm"
include "syl2anc.mm"
include "sylan.mm"
include "ax-hvdistr1.mm"
include "mp3an1.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem hvsubass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A -h B ) -h C ) = ( A -h ( B +h C ) ) )

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
    cC
    cmv
    co
    #
    cA
    @5
    cC
    cmv
    co
    #
    cva
    co
    #
    cA
    cB
    cmv
    co
    #
    cC
    cmv
    co
    cA
    cB
    cC
    cva
    co
    #
    cmv
    co
    #
    @1
    @0
    @5
    chil
    wcel
    #
    @2
    @7
    @9
    wceq
    @4
    cc
    wcel
    #
    @1
    @13
    neg1cn
    @4
    cB
    hvmulcl
    mpan
    #
    cA
    @5
    cC
    hvaddsubass
    syl3an2
    @3
    @10
    @6
    cC
    cmv
    @0
    @1
    @10
    @6
    wceq
    @2
    cA
    cB
    hvsubval
    3adant3
    oveq1d
    @3
    @12
    cA
    @4
    @11
    csm
    co
    #
    cva
    co
    #
    @9
    @3
    @0
    @11
    chil
    wcel
    #
    @12
    @17
    wceq
    @0
    @1
    @2
    simp1
    @1
    @2
    @18
    @0
    cB
    cC
    hvaddcl
    3adant1
    cA
    @11
    hvsubval
    syl2anc
    @3
    @8
    @16
    cA
    cva
    @3
    @8
    @5
    @4
    cC
    csm
    co
    cva
    co
    #
    @16
    @1
    @2
    @8
    @19
    wceq
    #
    @0
    @1
    @13
    @2
    @20
    @15
    @5
    cC
    hvsubval
    sylan
    3adant1
    @1
    @2
    @16
    @19
    wceq
    #
    @0
    @14
    @1
    @2
    @21
    neg1cn
    @4
    cB
    cC
    ax-hvdistr1
    mp3an1
    3adant1
    eqtr4d
    oveq2d
    eqtr4d
    3eqtr4d
end
