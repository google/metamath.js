include "cc0.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cneg.mm"
include "cdiv.mm"
include "halfnz.mm"
include "eleq1.mm"
include "mtbii.mm"
include "znegcl.mm"
include "nsyl3.mm"
include "eqcom.mm"
include "sylnibr.mm"
include "cc.mm"
include "wne.mm"
include "ax-1cn.mm"
include "2cn.mm"
include "2ne0.mm"
include "w3a.mm"
include "divneg.mm"
include "eqcomd.mm"
include "mp3an.mm"
include "a1i.mm"
include "eqeq1d.mm"
include "halfcn.mm"
include "zcn.mm"
include "negcon1d.mm"
include "bitrd.mm"
include "mtbird.mm"
include "neg1cn.mm"
include "2cnd.mm"
include "divmul2d.mm"
include "mtbid.mm"
include "cmin.mm"
include "wb.mm"
include "0cnd.mm"
include "1cnd.mm"
include "mulcld.mm"
include "subadd2.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "df-neg.mm"
include "eqcomi.mm"
include "3bitrd.mm"
include "nrex.mm"
include "intnan.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "mtbir.mm"
include "nelir.mm"

theorem 0nodd
  let vx: setvar x
  let vz: setvar z
  let cO: class O
  let vk: setvar k
  assume oddinmgm.e: |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) }

  disjoint x z
  disjoint k x
  assert |- 0 e/ O

  proof
    cc0
    cO
    cc0
    cO
    wcel
    cc0
    cz
    wcel
    #
    cc0
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
    cneg
    #
    @2
    wceq
    #
    @6
    @7
    c2
    cdiv
    co
    #
    @1
    wceq
    #
    @8
    @6
    @10
    @1
    cneg
    #
    c1
    c2
    cdiv
    co
    #
    wceq
    #
    @6
    @12
    @11
    wceq
    #
    @13
    @14
    @11
    cz
    wcel
    #
    @6
    @14
    @12
    cz
    wcel
    @15
    halfnz
    @12
    @11
    cz
    eleq1
    mtbii
    @1
    znegcl
    nsyl3
    @11
    @12
    eqcom
    sylnibr
    @6
    @10
    @12
    cneg
    #
    @1
    wceq
    @13
    @6
    @9
    @16
    @1
    @9
    @16
    wceq
    #
    @6
    c1
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
    @17
    ax-1cn
    2cn
    2ne0
    @18
    @19
    @20
    w3a
    @16
    @9
    c1
    c2
    divneg
    eqcomd
    mp3an
    a1i
    eqeq1d
    @6
    @12
    @1
    @12
    cc
    wcel
    @6
    halfcn
    a1i
    @1
    zcn
    #
    negcon1d
    bitrd
    mtbird
    @6
    @7
    @1
    c2
    @7
    cc
    wcel
    @6
    neg1cn
    a1i
    @21
    @6
    2cnd
    #
    @20
    @6
    2ne0
    a1i
    divmul2d
    mtbid
    @6
    @4
    @3
    cc0
    wceq
    #
    cc0
    c1
    cmin
    co
    #
    @2
    wceq
    #
    @8
    @4
    @23
    wb
    @6
    cc0
    @3
    eqcom
    a1i
    @6
    cc0
    cc
    wcel
    #
    @18
    @2
    cc
    wcel
    #
    @23
    @25
    wb
    @6
    0cnd
    @6
    1cnd
    @6
    c2
    @1
    @22
    @21
    mulcld
    @26
    @18
    @27
    w3a
    @25
    @23
    cc0
    c1
    @2
    subadd2
    bicomd
    syl3anc
    @6
    @24
    @7
    @2
    @24
    @7
    wceq
    @6
    @7
    @24
    c1
    df-neg
    eqcomi
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
    cc0
    cz
    cO
    @28
    cc0
    wceq
    @29
    @4
    vx
    cz
    @28
    cc0
    @3
    eqeq1
    rexbidv
    oddinmgm.e
    elrab2
    mtbir
    nelir
end
