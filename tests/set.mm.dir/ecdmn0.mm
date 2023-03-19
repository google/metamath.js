include "cdm.mm"
include "wcel.mm"
include "cvv.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "elex.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "ecexr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "wbr.mm"
include "wb.mm"
include "vex.mm"
include "elecg.mm"
include "mpan.mm"
include "exbidv.mm"
include "a1i.mm"
include "eldmg.mm"
include "3bitr4rd.mm"
include "pm5.21nii.mm"

theorem ecdmn0
  let cA: class A
  let cR: class R
  let vx: setvar x


  assert |- ( A e. dom R <-> [ A ] R =/= (/) )

  proof
    cA
    cR
    cdm
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cR
    cec
    #
    c0
    wne
    #
    cA
    @0
    elex
    @4
    vx
    cv
    #
    @3
    wcel
    #
    vx
    wex
    #
    @2
    vx
    @3
    n0
    #
    @6
    @2
    vx
    @5
    cA
    cR
    ecexr
    exlimiv
    sylbi
    @2
    @7
    cA
    @5
    cR
    wbr
    #
    vx
    wex
    @4
    @1
    @2
    @6
    @9
    vx
    @5
    cvv
    wcel
    @2
    @6
    @9
    wb
    vx
    vex
    @5
    cA
    cR
    cvv
    cvv
    elecg
    mpan
    exbidv
    @4
    @7
    wb
    @2
    @8
    a1i
    vx
    cA
    cR
    cvv
    eldmg
    3bitr4rd
    pm5.21nii
end
