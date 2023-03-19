include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "chil.mm"
include "w3a.mm"
include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "wceq.mm"
include "wo.mm"
include "csm.mm"
include "wb.mm"
include "wn.mm"
include "df-ne.mm"
include "biorf.mm"
include "sylbi.mm"
include "ad2antlr.mm"
include "3adant3.mm"
include "hvsubeq0.mm"
include "3adant1.mm"
include "hvsubdistr1.mm"
include "eqeq1d.mm"
include "hvsubcl.mm"
include "hvmul0or.mm"
include "sylan2.mm"
include "3impb.mm"
include "hvmulcl.mm"
include "3adant2.mm"
include "syl2anc.mm"
include "3bitr3d.mm"
include "3adant1r.mm"
include "3bitr3rd.mm"

theorem hvmulcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ B e. ~H /\ C e. ~H ) -> ( ( A .h B ) = ( A .h C ) <-> B = C ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
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
    cB
    cC
    cmv
    co
    #
    c0v
    wceq
    #
    cA
    cc0
    wceq
    #
    @6
    wo
    #
    cB
    cC
    wceq
    #
    cA
    cB
    csm
    co
    #
    cA
    cC
    csm
    co
    #
    wceq
    #
    @2
    @3
    @6
    @8
    wb
    #
    @4
    @1
    @13
    @0
    @3
    @1
    @7
    wn
    @13
    cA
    cc0
    df-ne
    @7
    @6
    biorf
    sylbi
    ad2antlr
    3adant3
    @3
    @4
    @6
    @9
    wb
    @2
    cB
    cC
    hvsubeq0
    3adant1
    @0
    @3
    @4
    @8
    @12
    wb
    @1
    @0
    @3
    @4
    w3a
    #
    cA
    @5
    csm
    co
    #
    c0v
    wceq
    #
    @10
    @11
    cmv
    co
    #
    c0v
    wceq
    #
    @8
    @12
    @14
    @15
    @17
    c0v
    cA
    cB
    cC
    hvsubdistr1
    eqeq1d
    @0
    @3
    @4
    @16
    @8
    wb
    #
    @3
    @4
    wa
    @0
    @5
    chil
    wcel
    @19
    cB
    cC
    hvsubcl
    cA
    @5
    hvmul0or
    sylan2
    3impb
    @14
    @10
    chil
    wcel
    #
    @11
    chil
    wcel
    #
    @18
    @12
    wb
    @0
    @3
    @20
    @4
    cA
    cB
    hvmulcl
    3adant3
    @0
    @4
    @21
    @3
    cA
    cC
    hvmulcl
    3adant2
    @10
    @11
    hvsubeq0
    syl2anc
    3bitr3d
    3adant1r
    3bitr3rd
end
