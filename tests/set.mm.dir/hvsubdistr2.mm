include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "cmv.mm"
include "c1.mm"
include "cneg.mm"
include "cva.mm"
include "cmin.mm"
include "wceq.mm"
include "hvmulcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "hvsubval.mm"
include "syl2anc.mm"
include "wa.mm"
include "cmul.mm"
include "mulm1.mm"
include "oveq1d.mm"
include "adantr.mm"
include "neg1cn.mm"
include "ax-hvmulass.mm"
include "mp3an1.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "caddc.mm"
include "negcl.mm"
include "ax-hvdistr2.mm"
include "syl3an2.mm"
include "negsub.mm"
include "3adant3.mm"
include "3eqtr2rd.mm"

theorem hvsubdistr2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. ~H ) -> ( ( A - B ) .h C ) = ( ( A .h C ) -h ( B .h C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    cA
    cC
    csm
    co
    #
    cB
    cC
    csm
    co
    #
    cmv
    co
    #
    @4
    c1
    cneg
    #
    @5
    csm
    co
    #
    cva
    co
    #
    @4
    cB
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
    cmin
    co
    #
    cC
    csm
    co
    #
    @3
    @4
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    @6
    @9
    wceq
    @0
    @2
    @15
    @1
    cA
    cC
    hvmulcl
    3adant2
    @1
    @2
    @16
    @0
    cB
    cC
    hvmulcl
    3adant1
    @4
    @5
    hvsubval
    syl2anc
    @3
    @11
    @8
    @4
    cva
    @1
    @2
    @11
    @8
    wceq
    @0
    @1
    @2
    wa
    @7
    cB
    cmul
    co
    #
    cC
    csm
    co
    #
    @11
    @8
    @1
    @18
    @11
    wceq
    @2
    @1
    @17
    @10
    cC
    csm
    cB
    mulm1
    oveq1d
    adantr
    @7
    cc
    wcel
    @1
    @2
    @18
    @8
    wceq
    neg1cn
    @7
    cB
    cC
    ax-hvmulass
    mp3an1
    eqtr3d
    3adant1
    oveq2d
    @3
    cA
    @10
    caddc
    co
    #
    cC
    csm
    co
    #
    @12
    @14
    @1
    @0
    @10
    cc
    wcel
    @2
    @20
    @12
    wceq
    cB
    negcl
    cA
    @10
    cC
    ax-hvdistr2
    syl3an2
    @3
    @19
    @13
    cC
    csm
    @0
    @1
    @19
    @13
    wceq
    @2
    cA
    cB
    negsub
    3adant3
    oveq1d
    eqtr3d
    3eqtr2rd
end
