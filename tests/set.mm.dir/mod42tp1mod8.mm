include "cz.mm"
include "wcel.mm"
include "c4.mm"
include "cmo.mm"
include "co.mm"
include "c3.mm"
include "wceq.mm"
include "c2.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "c8.mm"
include "c7.mm"
include "cv.mm"
include "wrex.mm"
include "cn.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "4nn.mm"
include "a1i.mm"
include "3nn0.mm"
include "3lt4.mm"
include "jctir.mm"
include "modremain.mm"
include "mpd3an23.mm"
include "c6.mm"
include "2cnd.mm"
include "simpr.mm"
include "4z.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "cc.mm"
include "3cn.mm"
include "adddid.mm"
include "4cn.mm"
include "mul12d.mm"
include "2cn.mm"
include "4t2e8.mm"
include "mulcomli.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "3t2e6.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "id.mm"
include "8nn.mm"
include "nnzi.mm"
include "6cn.mm"
include "1cnd.mm"
include "addassd.mm"
include "6p1e7.mm"
include "oveq2d.mm"
include "adantl.mm"
include "crp.mm"
include "cc0.mm"
include "cico.mm"
include "nnrp.mm"
include "mp1i.mm"
include "cxr.mm"
include "0xr.mm"
include "8re.mm"
include "rexri.mm"
include "7re.mm"
include "cle.mm"
include "0re.mm"
include "7pos.mm"
include "ltleii.mm"
include "7lt8.mm"
include "elicod.mm"
include "muladdmodid.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp.mm"

theorem mod42tp1mod8
  let cN: class N
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ ( N mod 4 ) = 3 ) -> ( ( ( 2 x. N ) + 1 ) mod 8 ) = 7 )

  proof
    cN
    cz
    wcel
    #
    cN
    c4
    cmo
    co
    c3
    wceq
    #
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    c8
    cmo
    co
    #
    c7
    wceq
    #
    @0
    @1
    vz
    cv
    #
    c4
    cmul
    co
    #
    c3
    caddc
    co
    #
    cN
    wceq
    #
    vz
    cz
    wrex
    #
    @5
    @0
    c4
    cn
    wcel
    #
    c3
    cn0
    wcel
    #
    c3
    c4
    clt
    wbr
    #
    wa
    @1
    @10
    wb
    @11
    @0
    4nn
    a1i
    @0
    @12
    @13
    @12
    @0
    3nn0
    a1i
    3lt4
    jctir
    vz
    c4
    c3
    cN
    modremain
    mpd3an23
    @0
    @9
    @5
    vz
    cz
    @0
    @6
    cz
    wcel
    #
    wa
    #
    c2
    @8
    cmul
    co
    #
    c1
    caddc
    co
    #
    c8
    cmo
    co
    #
    c7
    wceq
    @9
    @5
    @15
    @18
    @6
    c8
    cmul
    co
    #
    c7
    caddc
    co
    #
    c8
    cmo
    co
    #
    c7
    @15
    @17
    @20
    c8
    cmo
    @15
    @17
    @19
    c6
    caddc
    co
    #
    c1
    caddc
    co
    #
    @20
    @15
    @16
    @22
    c1
    caddc
    @15
    @16
    c2
    @7
    cmul
    co
    #
    c2
    c3
    cmul
    co
    #
    caddc
    co
    @22
    @15
    c2
    @7
    c3
    @15
    2cnd
    #
    @15
    @7
    @15
    @6
    c4
    @0
    @14
    simpr
    #
    c4
    cz
    wcel
    @15
    4z
    a1i
    zmulcld
    zcnd
    c3
    cc
    wcel
    @15
    3cn
    a1i
    adddid
    @15
    @24
    @19
    @25
    c6
    caddc
    @15
    @24
    @6
    c2
    c4
    cmul
    co
    #
    cmul
    co
    @19
    @15
    c2
    @6
    c4
    @26
    @15
    @6
    @27
    zcnd
    c4
    cc
    wcel
    @15
    4cn
    a1i
    mul12d
    @28
    c8
    @6
    cmul
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    oveq2i
    syl6eq
    @25
    c6
    wceq
    @15
    c3
    c2
    c6
    3cn
    2cn
    3t2e6
    mulcomli
    a1i
    oveq12d
    eqtrd
    oveq1d
    @14
    @23
    @20
    wceq
    @0
    @14
    @23
    @19
    c6
    c1
    caddc
    co
    #
    caddc
    co
    @20
    @14
    @19
    c6
    c1
    @14
    @19
    @14
    @6
    c8
    @14
    id
    c8
    cz
    wcel
    @14
    c8
    8nn
    nnzi
    a1i
    zmulcld
    zcnd
    c6
    cc
    wcel
    @14
    6cn
    a1i
    @14
    1cnd
    addassd
    @14
    @29
    c7
    @19
    caddc
    @29
    c7
    wceq
    @14
    6p1e7
    a1i
    oveq2d
    eqtrd
    adantl
    eqtrd
    oveq1d
    @14
    @21
    c7
    wceq
    #
    @0
    @14
    c8
    crp
    wcel
    #
    c7
    cc0
    c8
    cico
    co
    wcel
    @30
    c8
    cn
    wcel
    @31
    @14
    8nn
    c8
    nnrp
    mp1i
    @14
    cc0
    c8
    c7
    cc0
    cxr
    wcel
    @14
    0xr
    a1i
    c8
    cxr
    wcel
    @14
    c8
    8re
    rexri
    a1i
    c7
    cxr
    wcel
    @14
    c7
    7re
    rexri
    a1i
    cc0
    c7
    cle
    wbr
    @14
    cc0
    c7
    0re
    7re
    7pos
    ltleii
    a1i
    c7
    c8
    clt
    wbr
    @14
    7lt8
    a1i
    elicod
    c7
    c8
    @6
    muladdmodid
    mpd3an23
    adantl
    eqtrd
    @9
    @18
    @4
    c7
    @9
    @17
    @3
    c8
    cmo
    @9
    @16
    @2
    c1
    caddc
    @8
    cN
    c2
    cmul
    oveq2
    oveq1d
    oveq1d
    eqeq1d
    syl5ibcom
    rexlimdva
    sylbid
    imp
end
