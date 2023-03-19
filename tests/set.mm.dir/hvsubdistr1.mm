include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "wceq.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "ax-hvdistr1.mm"
include "syl3an3.mm"
include "wa.mm"
include "hvmulcom.mm"
include "mp3an2.mm"
include "oveq2d.mm"
include "3adant2.mm"
include "eqtrd.mm"
include "hvsubval.mm"
include "3adant1.mm"
include "3adant3.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"

theorem hvsubdistr1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( A .h ( B -h C ) ) = ( ( A .h B ) -h ( A .h C ) ) )

  proof
    cA
    cc
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
    csm
    co
    #
    cA
    cB
    csm
    co
    #
    @4
    cA
    cC
    csm
    co
    #
    csm
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
    csm
    co
    @8
    @9
    cmv
    co
    #
    @3
    @7
    @8
    cA
    @5
    csm
    co
    #
    cva
    co
    #
    @11
    @2
    @0
    @1
    @5
    chil
    wcel
    #
    @7
    @15
    wceq
    @4
    cc
    wcel
    #
    @2
    @16
    neg1cn
    @4
    cC
    hvmulcl
    mpan
    cA
    cB
    @5
    ax-hvdistr1
    syl3an3
    @0
    @2
    @15
    @11
    wceq
    @1
    @0
    @2
    wa
    @14
    @10
    @8
    cva
    @0
    @17
    @2
    @14
    @10
    wceq
    neg1cn
    cA
    @4
    cC
    hvmulcom
    mp3an2
    oveq2d
    3adant2
    eqtrd
    @3
    @12
    @6
    cA
    csm
    @1
    @2
    @12
    @6
    wceq
    @0
    cB
    cC
    hvsubval
    3adant1
    oveq2d
    @3
    @8
    chil
    wcel
    #
    @9
    chil
    wcel
    #
    @13
    @11
    wceq
    @0
    @1
    @18
    @2
    cA
    cB
    hvmulcl
    3adant3
    @0
    @2
    @19
    @1
    cA
    cC
    hvmulcl
    3adant2
    @8
    @9
    hvsubval
    syl2anc
    3eqtr4d
end
