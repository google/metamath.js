include "ceven.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "crab.mm"
include "cmul.mm"
include "wceq.mm"
include "wrex.mm"
include "df-even.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "oveq1.mm"
include "divcan3d.mm"
include "sylan9eqr.mm"
include "eqeltrd.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfeven4
  let vz: setvar z
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x

  disjoint i z
  disjoint k x
  assert |- Even = { z e. ZZ | E. i e. ZZ z = ( 2 x. i ) }

  proof
    ceven
    vz
    cv
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    vz
    cz
    crab
    @0
    c2
    vi
    cv
    #
    cmul
    co
    #
    wceq
    #
    vi
    cz
    wrex
    #
    vz
    cz
    crab
    vz
    df-even
    @2
    @6
    vz
    cz
    @0
    cz
    wcel
    #
    @2
    @6
    @7
    @2
    @6
    @7
    @2
    wa
    #
    @5
    @0
    c2
    @1
    cmul
    co
    #
    wceq
    #
    vi
    @1
    cz
    @7
    @2
    simpr
    @3
    @1
    wceq
    #
    @5
    @10
    wb
    @8
    @11
    @4
    @9
    @0
    @3
    @1
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @8
    @9
    @0
    @8
    @0
    c2
    @7
    @0
    cc
    wcel
    @2
    @0
    zcn
    adantr
    @8
    2cnd
    c2
    cc0
    wne
    #
    @8
    2ne0
    a1i
    divcan2d
    eqcomd
    rspcedvd
    ex
    @7
    @5
    @2
    vi
    cz
    @7
    @3
    cz
    wcel
    #
    wa
    #
    @5
    @2
    @14
    @5
    wa
    @1
    @3
    cz
    @5
    @14
    @1
    @4
    c2
    cdiv
    co
    @3
    @0
    @4
    c2
    cdiv
    oveq1
    @14
    @3
    c2
    @13
    @3
    cc
    wcel
    @7
    @3
    zcn
    adantl
    @14
    2cnd
    @12
    @14
    2ne0
    a1i
    divcan3d
    sylan9eqr
    @14
    @13
    @5
    @7
    @13
    simpr
    adantr
    eqeltrd
    ex
    rexlimdva
    impbid
    rabbiia
    eqtri
end
