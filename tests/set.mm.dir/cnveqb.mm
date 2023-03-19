include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "ccnv.mm"
include "cnveq.mm"
include "wi.mm"
include "dfrel2.mm"
include "eqeq2.mm"
include "syl5ibr.mm"
include "eqcoms.mm"
include "sylbi.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "imp.mm"
include "impbid2.mm"

theorem cnveqb
  let cA: class A
  let cB: class B


  assert |- ( ( Rel A /\ Rel B ) -> ( A = B <-> `' A = `' B ) )

  proof
    cA
    wrel
    #
    cB
    wrel
    #
    wa
    cA
    cB
    wceq
    #
    cA
    ccnv
    #
    cB
    ccnv
    #
    wceq
    #
    cA
    cB
    cnveq
    @0
    @1
    @5
    @2
    wi
    #
    @0
    @3
    ccnv
    #
    cA
    wceq
    @1
    @6
    wi
    #
    cA
    dfrel2
    @8
    cA
    @7
    @1
    @6
    cA
    @7
    wceq
    #
    @5
    @7
    cB
    wceq
    #
    wi
    #
    @1
    @4
    ccnv
    #
    cB
    wceq
    @11
    cB
    dfrel2
    @11
    cB
    @12
    @5
    @10
    cB
    @12
    wceq
    @7
    @12
    wceq
    @3
    @4
    cnveq
    cB
    @12
    @7
    eqeq2
    syl5ibr
    eqcoms
    sylbi
    @9
    @2
    @10
    @5
    cA
    @7
    cB
    eqeq1
    imbi2d
    syl5ibr
    eqcoms
    sylbi
    imp
    impbid2
end
