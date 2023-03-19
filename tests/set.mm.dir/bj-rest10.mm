include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "elrest.mm"
include "mpan2.mm"
include "in0.mm"
include "eqeq2i.mm"
include "rexbii.mm"
include "wex.mm"
include "df-rex.mm"
include "19.41v.mm"
include "n0.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "bitri.mm"
include "baib.mm"
include "sylan9bb.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "ex.mm"

theorem bj-rest10
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( X e. V -> ( X =/= (/) -> ( X |`t (/) ) = { (/) } ) )

  proof
    cX
    cV
    wcel
    #
    cX
    c0
    wne
    #
    cX
    c0
    crest
    co
    #
    c0
    csn
    #
    wceq
    @0
    @1
    wa
    #
    vx
    @2
    @3
    @4
    vx
    cv
    #
    @2
    wcel
    #
    @5
    c0
    wceq
    #
    @5
    @3
    wcel
    @0
    @6
    @5
    vy
    cv
    #
    c0
    cin
    #
    wceq
    #
    vy
    cX
    wrex
    #
    @1
    @7
    @0
    c0
    cvv
    wcel
    @6
    @11
    wb
    0ex
    vy
    @5
    c0
    cX
    cV
    cvv
    elrest
    mpan2
    @11
    @1
    @7
    @11
    @7
    vy
    cX
    wrex
    #
    @1
    @7
    wa
    #
    @10
    @7
    vy
    cX
    @9
    c0
    @5
    @8
    in0
    eqeq2i
    rexbii
    @12
    @8
    cX
    wcel
    #
    @7
    wa
    vy
    wex
    #
    @13
    @7
    vy
    cX
    df-rex
    @15
    @14
    vy
    wex
    #
    @7
    wa
    @13
    @14
    @7
    vy
    19.41v
    @16
    @1
    @7
    @1
    @16
    vy
    cX
    n0
    bicomi
    anbi1i
    bitri
    bitri
    bitri
    baib
    sylan9bb
    vx
    c0
    velsn
    syl6bbr
    eqrdv
    ex
end
