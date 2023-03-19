include "csingles.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "elex.mm"
include "snex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "exlimiv.mm"
include "eqeq1.mm"
include "exbidv.mm"
include "csingle.mm"
include "crn.mm"
include "wbr.mm"
include "df-singles.mm"
include "eleq2i.mm"
include "vex.mm"
include "elrn.mm"
include "brsingle.mm"
include "exbii.mm"
include "3bitri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem elsingles
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. Singletons <-> E. x A = { x } )

  proof
    cA
    csingles
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    #
    cA
    csingles
    elex
    @4
    @1
    vx
    @4
    @1
    @3
    cvv
    wcel
    @2
    snex
    cA
    @3
    cvv
    eleq1
    mpbiri
    exlimiv
    vy
    cv
    #
    csingles
    wcel
    #
    @6
    @3
    wceq
    #
    vx
    wex
    #
    @0
    @5
    vy
    cA
    cvv
    @6
    cA
    csingles
    eleq1
    @6
    cA
    wceq
    @8
    @4
    vx
    @6
    cA
    @3
    eqeq1
    exbidv
    @7
    @6
    csingle
    crn
    #
    wcel
    @2
    @6
    csingle
    wbr
    #
    vx
    wex
    @9
    csingles
    @10
    @6
    df-singles
    eleq2i
    vx
    @6
    csingle
    vy
    vex
    #
    elrn
    @11
    @8
    vx
    @2
    @6
    vx
    vex
    @12
    brsingle
    exbii
    3bitri
    vtoclbg
    pm5.21nii
end
