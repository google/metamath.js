include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "ccj.mm"
include "cfv.mm"
include "ax-his1.mm"
include "eqeqan12d.mm"
include "cc.mm"
include "hicl.mm"
include "ancoms.mm"
include "cj11.mm"
include "syl2an.mm"
include "bitr2d.mm"
include "anandirs.mm"
include "ralbidva.mm"
include "hial2eq.mm"
include "bitrd.mm"

theorem hial2eq2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A. x e. ~H ( x .ih A ) = ( x .ih B ) <-> A = B ) )

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
    vx
    cv
    #
    cA
    csp
    co
    #
    @3
    cB
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    cA
    @3
    csp
    co
    #
    cB
    @3
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    cA
    cB
    wceq
    @2
    @6
    @9
    vx
    chil
    @0
    @1
    @3
    chil
    wcel
    #
    @6
    @9
    wb
    @0
    @10
    wa
    #
    @1
    @10
    wa
    #
    wa
    @9
    @4
    ccj
    cfv
    #
    @5
    ccj
    cfv
    #
    wceq
    #
    @6
    @11
    @12
    @7
    @13
    @8
    @14
    cA
    @3
    ax-his1
    cB
    @3
    ax-his1
    eqeqan12d
    @11
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @15
    @6
    wb
    @12
    @10
    @0
    @16
    @3
    cA
    hicl
    ancoms
    @10
    @1
    @17
    @3
    cB
    hicl
    ancoms
    @4
    @5
    cj11
    syl2an
    bitr2d
    anandirs
    ralbidva
    vx
    cA
    cB
    hial2eq
    bitrd
end
