include "com.mm"
include "cv.mm"
include "wlim.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "con0.mm"
include "crab.mm"
include "csuc.mm"
include "wn.mm"
include "wss.mm"
include "df-om.mm"
include "wa.mm"
include "wb.mm"
include "onsssuc.mm"
include "ontri1.mm"
include "bitr3d.mm"
include "ancoms.mm"
include "weq.mm"
include "limeq.mm"
include "notbid.mm"
include "elrab.mm"
include "a1i.mm"
include "imbi12d.mm"
include "pm5.74da.mm"
include "cvv.mm"
include "vex.mm"
include "limelon.mm"
include "mpan.mm"
include "pm4.71ri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "con34b.mm"
include "ibar.mm"
include "imbi2d.mm"
include "syl5bb.mm"
include "pm5.74i.mm"
include "3bitri.mm"
include "syl6rbbr.mm"
include "simpr.mm"
include "suceloni.mm"
include "onelon.mm"
include "ex.mm"
include "syl.mm"
include "ancrd.mm"
include "impbid2.mm"
include "imbi1d.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "albidv.mm"
include "dfss2.mm"
include "syl6bbr.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfom2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- _om = { x e. On | suc x C_ { y e. On | -. Lim y } }

  proof
    com
    vz
    cv
    #
    wlim
    #
    vx
    cv
    #
    @0
    wcel
    #
    wi
    #
    vz
    wal
    #
    vx
    con0
    crab
    @2
    csuc
    #
    vy
    cv
    #
    wlim
    #
    wn
    #
    vy
    con0
    crab
    #
    wss
    #
    vx
    con0
    crab
    vx
    vz
    df-om
    @5
    @11
    vx
    con0
    @2
    con0
    wcel
    #
    @5
    @0
    @6
    wcel
    #
    @0
    @10
    wcel
    #
    wi
    #
    vz
    wal
    @11
    @12
    @4
    @15
    vz
    @12
    @4
    @0
    con0
    wcel
    #
    @15
    wi
    #
    @15
    @12
    @17
    @16
    @3
    wn
    #
    @16
    @1
    wn
    #
    wa
    #
    wi
    #
    wi
    #
    @4
    @12
    @16
    @15
    @21
    @12
    @16
    wa
    #
    @13
    @18
    @14
    @20
    @16
    @12
    @13
    @18
    wb
    @16
    @12
    wa
    @0
    @2
    wss
    @13
    @18
    @0
    @2
    onsssuc
    @0
    @2
    ontri1
    bitr3d
    ancoms
    @14
    @20
    wb
    @23
    @9
    @19
    vy
    @0
    con0
    vy
    vz
    weq
    @8
    @1
    @7
    @0
    limeq
    notbid
    elrab
    a1i
    imbi12d
    pm5.74da
    @4
    @16
    @1
    wa
    #
    @3
    wi
    @16
    @4
    wi
    @22
    @1
    @24
    @3
    @1
    @16
    @0
    cvv
    wcel
    @1
    @16
    vz
    vex
    @0
    cvv
    limelon
    mpan
    pm4.71ri
    imbi1i
    @16
    @1
    @3
    impexp
    @16
    @4
    @21
    @4
    @18
    @19
    wi
    @16
    @21
    @1
    @3
    con34b
    @16
    @19
    @20
    @18
    @16
    @19
    ibar
    imbi2d
    syl5bb
    pm5.74i
    3bitri
    syl6rbbr
    @17
    @16
    @13
    wa
    #
    @14
    wi
    @12
    @15
    @16
    @13
    @14
    impexp
    @12
    @25
    @13
    @14
    @12
    @25
    @13
    @16
    @13
    simpr
    @12
    @13
    @16
    @12
    @6
    con0
    wcel
    #
    @13
    @16
    wi
    @2
    suceloni
    @26
    @13
    @16
    @6
    @0
    onelon
    ex
    syl
    ancrd
    impbid2
    imbi1d
    syl5bbr
    bitrd
    albidv
    vz
    @6
    @10
    dfss2
    syl6bbr
    rabbiia
    eqtri
end
