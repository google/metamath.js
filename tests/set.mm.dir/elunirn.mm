include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wfun.mm"
include "cfv.mm"
include "cdm.mm"
include "wrex.mm"
include "eluni.mm"
include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "funfn.mm"
include "fvelrnb.mm"
include "sylbi.mm"
include "anbi2d.mm"
include "r19.42v.mm"
include "syl6bbr.mm"
include "eleq2.mm"
include "biimparc.mm"
include "reximi.mm"
include "syl6bi.mm"
include "exlimdv.mm"
include "fvelrn.mm"
include "a1d.mm"
include "ancld.mm"
include "fvex.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem elunirn
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  assert |- ( Fun F -> ( A e. U. ran F <-> E. x e. dom F A e. ( F ` x ) ) )

  proof
    cA
    cF
    crn
    #
    cuni
    wcel
    cA
    vy
    cv
    #
    wcel
    #
    @1
    @0
    wcel
    #
    wa
    #
    vy
    wex
    #
    cF
    wfun
    #
    cA
    vx
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vx
    cF
    cdm
    #
    wrex
    #
    vy
    cA
    @0
    eluni
    @6
    @5
    @11
    @6
    @4
    @11
    vy
    @6
    @4
    @2
    @8
    @1
    wceq
    #
    wa
    #
    vx
    @10
    wrex
    #
    @11
    @6
    @4
    @2
    @12
    vx
    @10
    wrex
    #
    wa
    @14
    @6
    @3
    @15
    @2
    @6
    cF
    @10
    wfn
    @3
    @15
    wb
    cF
    funfn
    vx
    @10
    @1
    cF
    fvelrnb
    sylbi
    anbi2d
    @2
    @12
    vx
    @10
    r19.42v
    syl6bbr
    @13
    @9
    vx
    @10
    @12
    @9
    @2
    @8
    @1
    cA
    eleq2
    biimparc
    reximi
    syl6bi
    exlimdv
    @6
    @9
    @5
    vx
    @10
    @6
    @7
    @10
    wcel
    wa
    #
    @9
    @9
    @8
    @0
    wcel
    #
    wa
    #
    @5
    @16
    @9
    @17
    @16
    @17
    @9
    @7
    cF
    fvelrn
    a1d
    ancld
    @4
    @18
    vy
    @8
    @7
    cF
    fvex
    @1
    @8
    wceq
    @2
    @9
    @3
    @17
    @1
    @8
    cA
    eleq2
    @1
    @8
    @0
    eleq1
    anbi12d
    spcev
    syl6
    rexlimdva
    impbid
    syl5bb
end
