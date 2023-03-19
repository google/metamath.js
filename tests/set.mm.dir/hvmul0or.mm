include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csm.mm"
include "co.mm"
include "c0v.mm"
include "wceq.mm"
include "cc0.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "c1.mm"
include "cdiv.mm"
include "oveq2.mm"
include "ad2antlr.mm"
include "cmul.mm"
include "recid2.mm"
include "oveq1d.mm"
include "adantlr.mm"
include "reccl.mm"
include "simpll.mm"
include "simplr.mm"
include "ax-hvmulass.mm"
include "syl3anc.mm"
include "ax-hvmulid.mm"
include "3eqtr3d.mm"
include "hvmul0.mm"
include "syl.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"
include "wi.mm"
include "ax-hvmul0.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "adantl.mm"
include "adantr.mm"
include "jaod.mm"
include "impbid.mm"

theorem hvmul0or
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( ( A .h B ) = 0h <-> ( A = 0 \/ B = 0h ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    csm
    co
    #
    c0v
    wceq
    #
    cA
    cc0
    wceq
    #
    cB
    c0v
    wceq
    #
    wo
    #
    @2
    @4
    @7
    @2
    @4
    wa
    #
    @5
    @6
    @5
    wn
    cA
    cc0
    wne
    #
    @8
    @6
    cA
    cc0
    df-ne
    @8
    @9
    @6
    @8
    @9
    wa
    c1
    cA
    cdiv
    co
    #
    @3
    csm
    co
    #
    @10
    c0v
    csm
    co
    #
    cB
    c0v
    @4
    @11
    @12
    wceq
    @2
    @9
    @3
    c0v
    @10
    csm
    oveq2
    ad2antlr
    @2
    @9
    @11
    cB
    wceq
    @4
    @2
    @9
    wa
    #
    @10
    cA
    cmul
    co
    #
    cB
    csm
    co
    #
    c1
    cB
    csm
    co
    #
    @11
    cB
    @0
    @9
    @15
    @16
    wceq
    @1
    @0
    @9
    wa
    #
    @14
    c1
    cB
    csm
    cA
    recid2
    oveq1d
    adantlr
    @13
    @10
    cc
    wcel
    #
    @0
    @1
    @15
    @11
    wceq
    @0
    @9
    @18
    @1
    cA
    reccl
    #
    adantlr
    @0
    @1
    @9
    simpll
    @0
    @1
    @9
    simplr
    @10
    cA
    cB
    ax-hvmulass
    syl3anc
    @1
    @16
    cB
    wceq
    @0
    @9
    cB
    ax-hvmulid
    ad2antlr
    3eqtr3d
    adantlr
    @2
    @9
    @12
    c0v
    wceq
    #
    @4
    @0
    @9
    @20
    @1
    @17
    @18
    @20
    @19
    @10
    hvmul0
    syl
    adantlr
    adantlr
    3eqtr3d
    ex
    syl5bir
    orrd
    ex
    @2
    @5
    @4
    @6
    @1
    @5
    @4
    wi
    @0
    @1
    @4
    @5
    cc0
    cB
    csm
    co
    #
    c0v
    wceq
    cB
    ax-hvmul0
    @5
    @3
    @21
    c0v
    cA
    cc0
    cB
    csm
    oveq1
    eqeq1d
    syl5ibrcom
    adantl
    @0
    @6
    @4
    wi
    @1
    @0
    @4
    @6
    cA
    c0v
    csm
    co
    #
    c0v
    wceq
    cA
    hvmul0
    @6
    @3
    @22
    c0v
    cB
    c0v
    cA
    csm
    oveq2
    eqeq1d
    syl5ibrcom
    adantr
    jaod
    impbid
end
