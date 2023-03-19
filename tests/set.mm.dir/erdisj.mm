include "wer.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "neq0.mm"
include "wa.mm"
include "simpl.mm"
include "wbr.mm"
include "elin.mm"
include "simplbi.mm"
include "adantl.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "ecexr.mm"
include "syl.mm"
include "elecg.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simprbi.mm"
include "ertr4d.mm"
include "erthi.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "orrd.mm"
include "orcomd.mm"

theorem erdisj
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vx: setvar x


  assert |- ( R Er X -> ( [ A ] R = [ B ] R \/ ( [ A ] R i^i [ B ] R ) = (/) ) )

  proof
    cX
    cR
    wer
    #
    cA
    cR
    cec
    #
    cB
    cR
    cec
    #
    cin
    #
    c0
    wceq
    #
    @1
    @2
    wceq
    #
    @0
    @4
    @5
    @4
    wn
    vx
    cv
    #
    @3
    wcel
    #
    vx
    wex
    @0
    @5
    vx
    @3
    neq0
    @0
    @7
    @5
    vx
    @0
    @7
    @5
    @0
    @7
    wa
    #
    cA
    cB
    cR
    cX
    @0
    @7
    simpl
    #
    @8
    cA
    @6
    cB
    cR
    cX
    @9
    @8
    @6
    @1
    wcel
    #
    cA
    @6
    cR
    wbr
    #
    @7
    @10
    @0
    @7
    @10
    @6
    @2
    wcel
    #
    @6
    @1
    @2
    elin
    #
    simplbi
    adantl
    #
    @8
    @6
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @10
    @11
    wb
    vx
    vex
    #
    @8
    @10
    @16
    @14
    @6
    cA
    cR
    ecexr
    syl
    @6
    cA
    cR
    cvv
    cvv
    elecg
    sylancr
    mpbid
    @8
    @12
    cB
    @6
    cR
    wbr
    #
    @7
    @12
    @0
    @7
    @10
    @12
    @13
    simprbi
    adantl
    #
    @8
    @15
    cB
    cvv
    wcel
    #
    @12
    @18
    wb
    @17
    @8
    @12
    @20
    @19
    @6
    cB
    cR
    ecexr
    syl
    @6
    cB
    cR
    cvv
    cvv
    elecg
    sylancr
    mpbid
    ertr4d
    erthi
    ex
    exlimdv
    syl5bi
    orrd
    orcomd
end
