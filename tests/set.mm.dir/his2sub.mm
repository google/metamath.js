include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cmv.mm"
include "co.mm"
include "csp.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "hvsubval.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "ax-his2.mm"
include "syl3an2.mm"
include "cmul.mm"
include "ax-his3.mm"
include "mp3an1.mm"
include "hicl.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "3adant2.mm"
include "negsubd.mm"
include "3eqtrd.mm"

theorem his2sub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A -h B ) .ih C ) = ( ( A .ih C ) - ( B .ih C ) ) )

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
    cmv
    co
    #
    cC
    csp
    co
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
    csp
    co
    #
    cA
    cC
    csp
    co
    #
    cB
    cC
    csp
    co
    #
    cneg
    #
    caddc
    co
    #
    @10
    @11
    cmin
    co
    @0
    @1
    @5
    @9
    wceq
    @2
    @0
    @1
    wa
    @4
    @8
    cC
    csp
    cA
    cB
    hvsubval
    oveq1d
    3adant3
    @3
    @9
    @10
    @7
    cC
    csp
    co
    #
    caddc
    co
    #
    @13
    @1
    @0
    @7
    chil
    wcel
    #
    @2
    @9
    @15
    wceq
    @6
    cc
    wcel
    #
    @1
    @16
    neg1cn
    @6
    cB
    hvmulcl
    mpan
    cA
    @7
    cC
    ax-his2
    syl3an2
    @1
    @2
    @15
    @13
    wceq
    @0
    @1
    @2
    wa
    #
    @14
    @12
    @10
    caddc
    @18
    @14
    @6
    @11
    cmul
    co
    #
    @12
    @17
    @1
    @2
    @14
    @19
    wceq
    neg1cn
    @6
    cB
    cC
    ax-his3
    mp3an1
    @18
    @11
    cB
    cC
    hicl
    #
    mulm1d
    eqtrd
    oveq2d
    3adant1
    eqtrd
    @3
    @10
    @11
    @0
    @2
    @10
    cc
    wcel
    @1
    cA
    cC
    hicl
    3adant2
    @1
    @2
    @11
    cc
    wcel
    @0
    @20
    3adant1
    negsubd
    3eqtrd
end
