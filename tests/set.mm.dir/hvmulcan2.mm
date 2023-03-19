include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "cmv.mm"
include "wceq.mm"
include "wb.mm"
include "hvmulcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "hvsubeq0.mm"
include "syl2anc.mm"
include "3adant3r.mm"
include "cmin.mm"
include "cc0.mm"
include "wo.mm"
include "hvsubdistr2.mm"
include "eqeq1d.mm"
include "subcl.mm"
include "hvmul0or.mm"
include "stoic3.mm"
include "bitr3d.mm"
include "wn.mm"
include "df-ne.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "sylbi.mm"
include "ad2antll.mm"
include "subeq0.mm"
include "3adant3.mm"
include "3bitr2d.mm"

theorem hvmulcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. ~H /\ C =/= 0h ) ) -> ( ( A .h C ) = ( B .h C ) <-> A = B ) )

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
    cC
    c0v
    wne
    #
    wa
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
    c0v
    wceq
    #
    @6
    @7
    wceq
    #
    cA
    cB
    wceq
    #
    @0
    @1
    @2
    @9
    @10
    wb
    #
    @3
    @0
    @1
    @2
    w3a
    #
    @6
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    @12
    @0
    @2
    @14
    @1
    cA
    cC
    hvmulcl
    3adant2
    @1
    @2
    @15
    @0
    cB
    cC
    hvmulcl
    3adant1
    @6
    @7
    hvsubeq0
    syl2anc
    3adant3r
    @5
    @9
    cA
    cB
    cmin
    co
    #
    cc0
    wceq
    #
    cC
    c0v
    wceq
    #
    wo
    #
    @17
    @11
    @0
    @1
    @2
    @9
    @19
    wb
    @3
    @13
    @16
    cC
    csm
    co
    #
    c0v
    wceq
    #
    @9
    @19
    @13
    @20
    @8
    c0v
    cA
    cB
    cC
    hvsubdistr2
    eqeq1d
    @0
    @1
    @16
    cc
    wcel
    @2
    @21
    @19
    wb
    cA
    cB
    subcl
    @16
    cC
    hvmul0or
    stoic3
    bitr3d
    3adant3r
    @1
    @4
    @17
    @19
    wb
    #
    @0
    @3
    @22
    @1
    @2
    @3
    @18
    wn
    #
    @22
    cC
    c0v
    df-ne
    @23
    @17
    @18
    @17
    wo
    @19
    @18
    @17
    biorf
    @18
    @17
    orcom
    syl6bb
    sylbi
    ad2antll
    3adant1
    @0
    @1
    @17
    @11
    wb
    @4
    cA
    cB
    subeq0
    3adant3
    3bitr2d
    bitr3d
end
