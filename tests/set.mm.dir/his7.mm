include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "csp.mm"
include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "ax-his2.mm"
include "fveq2d.mm"
include "wa.mm"
include "cc.mm"
include "hicl.mm"
include "cjadd.mm"
include "syl2an.mm"
include "3impdir.mm"
include "eqtrd.mm"
include "3comr.mm"
include "hvaddcl.mm"
include "ax-his1.mm"
include "sylan2.mm"
include "3impb.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem his7
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( A .ih ( B +h C ) ) = ( ( A .ih B ) + ( A .ih C ) ) )

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
    cB
    cC
    cva
    co
    #
    cA
    csp
    co
    #
    ccj
    cfv
    #
    cB
    cA
    csp
    co
    #
    ccj
    cfv
    #
    cC
    cA
    csp
    co
    #
    ccj
    cfv
    #
    caddc
    co
    #
    cA
    @4
    csp
    co
    #
    cA
    cB
    csp
    co
    #
    cA
    cC
    csp
    co
    #
    caddc
    co
    @1
    @2
    @0
    @6
    @11
    wceq
    @1
    @2
    @0
    w3a
    #
    @6
    @7
    @9
    caddc
    co
    #
    ccj
    cfv
    #
    @11
    @15
    @5
    @16
    ccj
    cB
    cC
    cA
    ax-his2
    fveq2d
    @1
    @0
    @2
    @17
    @11
    wceq
    #
    @1
    @0
    wa
    @7
    cc
    wcel
    @9
    cc
    wcel
    @18
    @2
    @0
    wa
    cB
    cA
    hicl
    cC
    cA
    hicl
    @7
    @9
    cjadd
    syl2an
    3impdir
    eqtrd
    3comr
    @0
    @1
    @2
    @12
    @6
    wceq
    #
    @1
    @2
    wa
    @0
    @4
    chil
    wcel
    @19
    cB
    cC
    hvaddcl
    cA
    @4
    ax-his1
    sylan2
    3impb
    @3
    @13
    @8
    @14
    @10
    caddc
    @0
    @1
    @13
    @8
    wceq
    @2
    cA
    cB
    ax-his1
    3adant3
    @0
    @2
    @14
    @10
    wceq
    @1
    cA
    cC
    ax-his1
    3adant2
    oveq12d
    3eqtr4d
end
