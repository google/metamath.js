include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cmv.mm"
include "co.mm"
include "csp.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "c0v.mm"
include "hvsubcl.mm"
include "his2sub.mm"
include "mpd3an3.mm"
include "eqeq1d.mm"
include "wb.mm"
include "his6.mm"
include "syl.mm"
include "bitr3d.mm"
include "cc.mm"
include "hicl.mm"
include "syldan.mm"
include "simpr.mm"
include "syl2anc.mm"
include "subeq0ad.mm"
include "hvsubeq0.mm"
include "3bitr3d.mm"

theorem hi2eq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A .ih ( A -h B ) ) = ( B .ih ( A -h B ) ) <-> A = B ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cmv
    co
    #
    csp
    co
    #
    cB
    @3
    csp
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @3
    c0v
    wceq
    #
    @4
    @5
    wceq
    cA
    cB
    wceq
    @2
    @3
    @3
    csp
    co
    #
    cc0
    wceq
    #
    @7
    @8
    @2
    @9
    @6
    cc0
    @0
    @1
    @3
    chil
    wcel
    #
    @9
    @6
    wceq
    cA
    cB
    hvsubcl
    #
    cA
    cB
    @3
    his2sub
    mpd3an3
    eqeq1d
    @2
    @11
    @10
    @8
    wb
    @12
    @3
    his6
    syl
    bitr3d
    @2
    @4
    @5
    @0
    @1
    @11
    @4
    cc
    wcel
    @12
    cA
    @3
    hicl
    syldan
    @2
    @1
    @11
    @5
    cc
    wcel
    @0
    @1
    simpr
    @12
    cB
    @3
    hicl
    syl2anc
    subeq0ad
    cA
    cB
    hvsubeq0
    3bitr3d
end
