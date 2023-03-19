include "codd.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "crab.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "dfodd2.mm"
include "wa.mm"
include "weq.mm"
include "simpr.mm"
include "oveq2.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "3jca.mm"
include "adantr.mm"
include "divcan2.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "zcn.mm"
include "npcan1.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "oveq1.mm"
include "mulcl.mm"
include "syl2an.mm"
include "pncan1.mm"
include "adantl.mm"
include "divcan3d.mm"
include "eqeltrd.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfodd6
  let vz: setvar z
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x

  disjoint i z
  disjoint k x
  assert |- Odd = { z e. ZZ | E. i e. ZZ z = ( ( 2 x. i ) + 1 ) }

  proof
    codd
    vz
    cv
    #
    c1
    cmin
    co
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
    c1
    caddc
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
    dfodd2
    @3
    @8
    vz
    cz
    @0
    cz
    wcel
    #
    @3
    @8
    @9
    @3
    @8
    @9
    @3
    wa
    #
    @7
    vz
    vz
    weq
    vi
    @2
    cz
    @9
    @3
    simpr
    @10
    @4
    @2
    wceq
    #
    wa
    #
    @6
    @0
    @0
    @12
    @6
    @1
    c1
    caddc
    co
    #
    @0
    @12
    @5
    @1
    c1
    caddc
    @11
    @10
    @5
    c2
    @2
    cmul
    co
    #
    @1
    @4
    @2
    c2
    cmul
    oveq2
    @10
    @1
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    w3a
    #
    @14
    @1
    wceq
    @9
    @18
    @3
    @9
    @15
    @16
    @17
    @9
    @1
    @0
    peano2zm
    zcnd
    @9
    2cnd
    #
    @17
    @9
    2ne0
    a1i
    3jca
    adantr
    @1
    c2
    divcan2
    syl
    sylan9eqr
    oveq1d
    @10
    @13
    @0
    wceq
    #
    @11
    @9
    @20
    @3
    @9
    @0
    cc
    wcel
    @20
    @0
    zcn
    @0
    npcan1
    syl
    adantr
    adantr
    eqtrd
    eqeq2d
    @10
    @0
    eqidd
    rspcedvd
    ex
    @9
    @7
    @3
    vi
    cz
    @9
    @4
    cz
    wcel
    #
    wa
    #
    @7
    @3
    @22
    @7
    wa
    #
    @2
    @4
    cz
    @23
    @2
    @5
    c2
    cdiv
    co
    #
    @4
    @23
    @1
    @5
    c2
    cdiv
    @7
    @22
    @1
    @6
    c1
    cmin
    co
    #
    @5
    @0
    @6
    c1
    cmin
    oveq1
    @22
    @5
    cc
    wcel
    #
    @25
    @5
    wceq
    @9
    @16
    @4
    cc
    wcel
    #
    @26
    @21
    @19
    @4
    zcn
    #
    c2
    @4
    mulcl
    syl2an
    @5
    pncan1
    syl
    sylan9eqr
    oveq1d
    @22
    @24
    @4
    wceq
    @7
    @22
    @4
    c2
    @21
    @27
    @9
    @28
    adantl
    @22
    2cnd
    @17
    @22
    2ne0
    a1i
    divcan3d
    adantr
    eqtrd
    @22
    @21
    @7
    @9
    @21
    simpr
    adantr
    eqeltrd
    ex
    rexlimdva
    impbid
    rabbiia
    eqtri
end
