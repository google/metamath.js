include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cdiv.mm"
include "wo.mm"
include "wi.mm"
include "zeo.mm"
include "wa.mm"
include "cc0.mm"
include "cr.mm"
include "crp.mm"
include "wb.mm"
include "zre.mm"
include "2rp.mm"
include "mod0.mm"
include "sylancl.mm"
include "biimpar.mm"
include "eqeq1.mm"
include "wne.mm"
include "0ne1.mm"
include "eqneqall.mm"
include "mpi.mm"
include "syl6bi.mm"
include "syl.mm"
include "expcom.mm"
include "cmin.mm"
include "peano2zm.mm"
include "cc.mm"
include "zcn.mm"
include "xp1d2m1eqxm1d2.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "mpan9.mm"
include "oveq2.mm"
include "adantl.mm"
include "oveq1d.mm"
include "zcnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "npcan1.mm"
include "eqtrd.mm"
include "ad2antlr.mm"
include "rspcedeq1vd.mm"
include "a1d.mm"
include "ex.mm"
include "jaoi.mm"
include "mpcom.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "mulcomd.mm"
include "mulmod0.mm"
include "mpan2.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "2z.mm"
include "id.mm"
include "zmulcld.mm"
include "zred.mm"
include "1red.mm"
include "modaddmod.mm"
include "syl3anc.mm"
include "clt.mm"
include "2re.mm"
include "1lt2.mm"
include "pm3.2i.mm"
include "1mod.mm"
include "mp1i.mm"
include "3eqtr3d.mm"
include "sylan9eqr.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "odd2np1.mm"
include "bitr4d.mm"

theorem mod2eq1n2dvds
  let cN: class N
  let vn: setvar n


  assert |- ( N e. ZZ -> ( ( N mod 2 ) = 1 <-> -. 2 || N ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    cmo
    co
    #
    c1
    wceq
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    c2
    cN
    cdvds
    wbr
    wn
    @0
    @2
    @7
    cN
    c2
    cdiv
    co
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wo
    @0
    @2
    @7
    wi
    #
    cN
    zeo
    @8
    @0
    @11
    wi
    @10
    @0
    @8
    @11
    @0
    @8
    wa
    @1
    cc0
    wceq
    #
    @11
    @0
    @12
    @8
    @0
    cN
    cr
    wcel
    c2
    crp
    wcel
    #
    @12
    @8
    wb
    cN
    zre
    2rp
    cN
    c2
    mod0
    sylancl
    biimpar
    @12
    @2
    cc0
    c1
    wceq
    #
    @7
    @1
    cc0
    c1
    eqeq1
    @14
    cc0
    c1
    wne
    @7
    0ne1
    @7
    cc0
    c1
    eqneqall
    mpi
    syl6bi
    syl
    expcom
    @10
    @0
    @11
    @10
    @0
    wa
    #
    @7
    @2
    @15
    vn
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cz
    @5
    cN
    @10
    @9
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @0
    @17
    cz
    wcel
    #
    @9
    peano2zm
    @0
    @19
    @20
    @0
    @18
    @17
    cz
    @0
    cN
    cc
    wcel
    #
    @18
    @17
    wceq
    cN
    zcn
    #
    cN
    xp1d2m1eqxm1d2
    syl
    eleq1d
    biimpd
    mpan9
    @15
    @3
    @17
    wceq
    #
    wa
    #
    @5
    c2
    @17
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    @24
    @4
    @25
    c1
    caddc
    @23
    @4
    @25
    wceq
    @15
    @3
    @17
    c2
    cmul
    oveq2
    adantl
    oveq1d
    @0
    @26
    cN
    wceq
    @10
    @23
    @0
    @26
    @16
    c1
    caddc
    co
    #
    cN
    @0
    @25
    @16
    c1
    caddc
    @0
    @16
    c2
    @0
    @16
    cN
    peano2zm
    zcnd
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan2d
    oveq1d
    @0
    @21
    @27
    cN
    wceq
    @22
    cN
    npcan1
    syl
    eqtrd
    ad2antlr
    eqtrd
    rspcedeq1vd
    a1d
    ex
    jaoi
    mpcom
    @0
    @6
    @2
    vn
    cz
    @0
    @3
    cz
    wcel
    #
    wa
    #
    @6
    @2
    @6
    @29
    @1
    @5
    c2
    cmo
    co
    #
    c1
    @1
    @30
    wceq
    cN
    @5
    cN
    @5
    c2
    cmo
    oveq1
    eqcoms
    @28
    @30
    c1
    wceq
    @0
    @28
    @4
    c2
    cmo
    co
    #
    c1
    caddc
    co
    #
    c2
    cmo
    co
    #
    c1
    c2
    cmo
    co
    #
    @30
    c1
    @28
    @32
    c1
    c2
    cmo
    @28
    @32
    cc0
    c1
    caddc
    co
    c1
    @28
    @31
    cc0
    c1
    caddc
    @28
    @31
    @3
    c2
    cmul
    co
    #
    c2
    cmo
    co
    #
    cc0
    @28
    @4
    @35
    c2
    cmo
    @28
    c2
    @3
    @28
    2cnd
    @3
    zcn
    mulcomd
    oveq1d
    @28
    @13
    @36
    cc0
    wceq
    2rp
    @3
    c2
    mulmod0
    mpan2
    eqtrd
    oveq1d
    0p1e1
    syl6eq
    oveq1d
    @28
    @4
    cr
    wcel
    c1
    cr
    wcel
    @13
    @33
    @30
    wceq
    @28
    @4
    @28
    c2
    @3
    c2
    cz
    wcel
    @28
    2z
    a1i
    @28
    id
    zmulcld
    zred
    @28
    1red
    @13
    @28
    2rp
    a1i
    @4
    c1
    c2
    modaddmod
    syl3anc
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    wa
    @34
    c1
    wceq
    @28
    @37
    @38
    2re
    1lt2
    pm3.2i
    c2
    1mod
    mp1i
    3eqtr3d
    adantl
    sylan9eqr
    ex
    rexlimdva
    impbid
    vn
    cN
    odd2np1
    bitr4d
end
