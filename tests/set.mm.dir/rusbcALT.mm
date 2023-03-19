include "cv.mm"
include "wnel.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wb.mm"
include "pm5.19.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcnel12g.mm"
include "sbc8g.mm"
include "df-nel.mm"
include "csbvarg.mm"
include "eleq12d.mm"
include "notbid.mm"
include "syl5bb.mm"
include "3bitr3d.mm"
include "mto.mm"
include "mpbir.mm"

theorem rusbcALT
  let vx: setvar x


  assert |- { x | x e/ x } e/ _V

  proof
    vx
    cv
    #
    @0
    wnel
    #
    vx
    cab
    #
    cvv
    wnel
    @2
    cvv
    wcel
    #
    wn
    @3
    @2
    @2
    wcel
    #
    @4
    wn
    #
    wb
    @4
    pm5.19
    @3
    @1
    vx
    @2
    wsbc
    vx
    @2
    @0
    csb
    #
    @6
    wnel
    #
    @4
    @5
    vx
    @2
    @0
    @0
    cvv
    sbcnel12g
    @1
    vx
    @2
    cvv
    sbc8g
    @7
    @6
    @6
    wcel
    #
    wn
    @3
    @5
    @6
    @6
    df-nel
    @3
    @8
    @4
    @3
    @6
    @2
    @6
    @2
    vx
    @2
    cvv
    csbvarg
    #
    @9
    eleq12d
    notbid
    syl5bb
    3bitr3d
    mto
    @2
    cvv
    df-nel
    mpbir
end
