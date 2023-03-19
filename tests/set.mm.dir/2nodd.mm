include "c2.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cdiv.mm"
include "halfnz.mm"
include "eleq1.mm"
include "mtbii.mm"
include "con2i.mm"
include "1cnd.mm"
include "zcn.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divmul2d.mm"
include "mtbid.mm"
include "cmin.mm"
include "wb.mm"
include "eqcom.mm"
include "cc.mm"
include "mulcld.mm"
include "w3a.mm"
include "subadd2.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "2m1e1.mm"
include "eqeq1d.mm"
include "3bitrd.mm"
include "mtbird.mm"
include "nrex.mm"
include "intnan.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "mtbir.mm"
include "nelir.mm"

theorem 2nodd
  let vx: setvar x
  let vz: setvar z
  let cO: class O
  let vk: setvar k
  assume oddinmgm.e: |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) }

  disjoint x z
  disjoint k x
  assert |- 2 e/ O

  proof
    c2
    cO
    c2
    cO
    wcel
    c2
    cz
    wcel
    #
    c2
    c2
    vx
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
    vx
    cz
    wrex
    #
    wa
    @5
    @0
    @4
    vx
    cz
    @1
    cz
    wcel
    #
    @4
    c1
    @2
    wceq
    #
    @6
    c1
    c2
    cdiv
    co
    #
    @1
    wceq
    #
    @7
    @9
    @6
    @9
    @8
    cz
    wcel
    @6
    halfnz
    @8
    @1
    cz
    eleq1
    mtbii
    con2i
    @6
    c1
    @1
    c2
    @6
    1cnd
    #
    @1
    zcn
    #
    @6
    2cnd
    #
    c2
    cc0
    wne
    @6
    2ne0
    a1i
    divmul2d
    mtbid
    @6
    @4
    @3
    c2
    wceq
    #
    c2
    c1
    cmin
    co
    #
    @2
    wceq
    #
    @7
    @4
    @13
    wb
    @6
    c2
    @3
    eqcom
    a1i
    @6
    c2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @13
    @15
    wb
    @12
    @10
    @6
    c2
    @1
    @12
    @11
    mulcld
    @16
    @17
    @18
    w3a
    @15
    @13
    c2
    c1
    @2
    subadd2
    bicomd
    syl3anc
    @6
    @14
    c1
    @2
    @14
    c1
    wceq
    @6
    2m1e1
    a1i
    eqeq1d
    3bitrd
    mtbird
    nrex
    intnan
    vz
    cv
    #
    @3
    wceq
    #
    vx
    cz
    wrex
    @5
    vz
    c2
    cz
    cO
    @19
    c2
    wceq
    @20
    @4
    vx
    cz
    @19
    c2
    @3
    eqeq1
    rexbidv
    oddinmgm.e
    elrab2
    mtbir
    nelir
end
