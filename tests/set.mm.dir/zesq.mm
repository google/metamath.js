include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "wa.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "sqval.mm"
include "syl.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divassd.mm"
include "eqtrd.mm"
include "adantr.mm"
include "zmulcl.mm"
include "eqeltrd.mm"
include "c1.mm"
include "caddc.mm"
include "wn.mm"
include "cmin.mm"
include "sqcl.mm"
include "peano2cn.mm"
include "halfcld.mm"
include "pncand.mm"
include "binom21.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "1cnd.mm"
include "add32d.mm"
include "3eqtr3d.mm"
include "divdird.mm"
include "divcan3d.mm"
include "oveq2d.mm"
include "peano2z.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "simpl.mm"
include "zsubcld.mm"
include "ex.mm"
include "con3d.mm"
include "wb.mm"
include "zsqcl.mm"
include "zeo2.mm"
include "3imtr4d.mm"
include "imp.mm"
include "impbida.mm"

theorem zesq
  let cN: class N


  assert |- ( N e. ZZ -> ( ( N / 2 ) e. ZZ <-> ( ( N ^ 2 ) / 2 ) e. ZZ ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cN
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    @2
    wa
    @4
    cN
    @1
    cmul
    co
    #
    cz
    @0
    @4
    @6
    wceq
    @2
    @0
    @4
    cN
    cN
    cmul
    co
    #
    c2
    cdiv
    co
    @6
    @0
    @3
    @7
    c2
    cdiv
    @0
    cN
    cc
    wcel
    #
    @3
    @7
    wceq
    cN
    zcn
    #
    cN
    sqval
    syl
    oveq1d
    @0
    cN
    cN
    c2
    @9
    @9
    @0
    2cnd
    c2
    cc0
    wne
    #
    @0
    2ne0
    a1i
    divassd
    eqtrd
    adantr
    cN
    @1
    zmulcl
    eqeltrd
    @0
    @5
    @2
    @0
    @3
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wn
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wn
    @5
    @2
    @0
    @17
    @13
    @0
    @17
    @13
    @0
    @17
    wa
    #
    @12
    cN
    caddc
    co
    #
    cN
    cmin
    co
    @12
    cz
    @18
    @12
    cN
    @18
    @11
    @18
    @3
    cc
    wcel
    #
    @11
    cc
    wcel
    @18
    @8
    @20
    @0
    @8
    @17
    @9
    adantr
    #
    cN
    sqcl
    syl
    #
    @3
    peano2cn
    syl
    #
    halfcld
    @21
    pncand
    @18
    @19
    cN
    @18
    @15
    @16
    cmul
    co
    #
    @19
    cz
    @18
    @15
    @15
    cmul
    co
    #
    c2
    cdiv
    co
    @11
    c2
    cN
    cmul
    co
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @24
    @19
    @18
    @25
    @27
    c2
    cdiv
    @18
    @15
    c2
    cexp
    co
    #
    @3
    @26
    caddc
    co
    c1
    caddc
    co
    #
    @25
    @27
    @18
    @8
    @29
    @30
    wceq
    @21
    cN
    binom21
    syl
    @18
    @15
    cc
    wcel
    #
    @29
    @25
    wceq
    @18
    @8
    @31
    @21
    cN
    peano2cn
    syl
    #
    @15
    sqval
    syl
    @18
    @3
    @26
    c1
    @22
    @18
    c2
    cc
    wcel
    @8
    @26
    cc
    wcel
    2cn
    @21
    c2
    cN
    mulcl
    sylancr
    #
    @18
    1cnd
    add32d
    3eqtr3d
    oveq1d
    @18
    @15
    @15
    c2
    @32
    @32
    @18
    2cnd
    #
    @10
    @18
    2ne0
    a1i
    #
    divassd
    @18
    @28
    @12
    @26
    c2
    cdiv
    co
    #
    caddc
    co
    @19
    @18
    @11
    @26
    c2
    @23
    @33
    @34
    @35
    divdird
    @18
    @36
    cN
    @12
    caddc
    @18
    cN
    c2
    @21
    @34
    @35
    divcan3d
    oveq2d
    eqtrd
    3eqtr3d
    @0
    @15
    cz
    wcel
    @17
    @24
    cz
    wcel
    cN
    peano2z
    @15
    @16
    zmulcl
    sylan
    eqeltrrd
    @0
    @17
    simpl
    zsubcld
    eqeltrrd
    ex
    con3d
    @0
    @3
    cz
    wcel
    @5
    @14
    wb
    cN
    zsqcl
    @3
    zeo2
    syl
    cN
    zeo2
    3imtr4d
    imp
    impbida
end
