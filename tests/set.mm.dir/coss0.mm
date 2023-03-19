include "c0.mm"
include "ccoss.mm"
include "cv.mm"
include "cec.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "dfcoss2.mm"
include "ec0.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "exbii.mm"
include "19.9v.mm"
include "bitri.mm"
include "opabbii.mm"
include "cpr.mm"
include "wss.mm"
include "wne.mm"
include "cvv.mm"
include "prnzg.mm"
include "elv.mm"
include "ss0b.mm"
include "nemtbir.mm"
include "wb.mm"
include "prssg.mm"
include "el2v.mm"
include "mtbir.mm"
include "opabf.mm"
include "3eqtri.mm"

theorem coss0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ,~ (/) = (/)

  proof
    c0
    ccoss
    vy
    cv
    #
    vx
    cv
    #
    c0
    cec
    #
    wcel
    #
    vz
    cv
    #
    @2
    wcel
    #
    wa
    #
    vx
    wex
    #
    vy
    vz
    copab
    @0
    c0
    wcel
    #
    @4
    c0
    wcel
    #
    wa
    #
    vy
    vz
    copab
    c0
    vy
    vz
    vx
    c0
    dfcoss2
    @7
    @10
    vy
    vz
    @7
    @10
    vx
    wex
    @10
    @6
    @10
    vx
    @3
    @8
    @5
    @9
    @2
    c0
    @0
    @1
    ec0
    #
    eleq2i
    @2
    c0
    @4
    @11
    eleq2i
    anbi12i
    exbii
    @10
    vx
    19.9v
    bitri
    opabbii
    @10
    vy
    vz
    @10
    @0
    @4
    cpr
    #
    c0
    wss
    #
    @13
    @12
    c0
    @12
    c0
    wne
    vy
    @0
    @4
    cvv
    prnzg
    elv
    @12
    ss0b
    nemtbir
    @10
    @13
    wb
    vy
    vz
    @0
    @4
    c0
    cvv
    cvv
    prssg
    el2v
    mtbir
    opabf
    3eqtri
end
