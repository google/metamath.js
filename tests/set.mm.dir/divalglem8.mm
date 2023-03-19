include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "w3a.mm"
include "cc0.mm"
include "caddc.mm"
include "wb.mm"
include "cc.mm"
include "cn0.mm"
include "cv.mm"
include "cdvds.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nn0sscn.mm"
include "sstri.mm"
include "sseli.mm"
include "wne.mm"
include "cn.mm"
include "nnabscl.mm"
include "mp2an.mm"
include "nnzi.mm"
include "zmulcl.mm"
include "mpan2.mm"
include "zcnd.mm"
include "subadd.mm"
include "syl3an.mm"
include "3com12.mm"
include "eqcom.mm"
include "3bitr3g.mm"
include "3adant1r.mm"
include "3adant2r.mm"
include "wn.mm"
include "c1.mm"
include "cfz.mm"
include "breq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "cle.mm"
include "elnn0z.mm"
include "sylib.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "0z.mm"
include "elfzm11.mm"
include "ex.mm"
include "vtoclga.mm"
include "biimpd.mm"
include "sylan9.mm"
include "impancom.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "divalglem7.mm"
include "sylan.mm"
include "3adant2.mm"
include "con2d.mm"
include "syld.mm"
include "df-ne.mm"
include "con2bii.mm"
include "syl6ibr.mm"
include "sylbid.mm"
include "oveq1.mm"
include "nncni.mm"
include "mul02i.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "biimpac.mm"
include "subeq0.mm"
include "syl2anr.mm"
include "syl5ib.mm"
include "ad2ant2r.mm"
include "3adant3.mm"
include "expd.mm"
include "mpdd.mm"
include "3expia.mm"
include "an4s.mm"

theorem divalglem8
  let cD: class D
  let cS: class S
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vq: setvar q
  let vx: setvar x
  let vz: setvar z
  assume divalglem8.1: |- N e. ZZ
  assume divalglem8.2: |- D e. ZZ
  assume divalglem8.3: |- D =/= 0
  assume divalglem8.4: |- S = { r e. NN0 | D || ( N - r ) }

  disjoint D r
  disjoint N r
  disjoint D q
  disjoint D x
  disjoint D z
  disjoint q r
  disjoint q x
  disjoint q z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint N q
  disjoint N x
  disjoint N z
  disjoint S x
  disjoint S z
  disjoint X z
  disjoint Y z
  assert |- ( ( ( X e. S /\ Y e. S ) /\ ( X < ( abs ` D ) /\ Y < ( abs ` D ) ) ) -> ( K e. ZZ -> ( ( K x. ( abs ` D ) ) = ( Y - X ) -> X = Y ) ) )

  proof
    cX
    cS
    wcel
    #
    cX
    cD
    cabs
    cfv
    #
    clt
    wbr
    #
    cY
    cS
    wcel
    #
    cY
    @1
    clt
    wbr
    #
    cK
    cz
    wcel
    #
    cK
    @1
    cmul
    co
    #
    cY
    cX
    cmin
    co
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wi
    #
    wi
    @0
    @2
    wa
    #
    @3
    @4
    wa
    #
    @5
    @10
    @11
    @12
    @5
    w3a
    #
    @8
    cK
    cc0
    wceq
    #
    @9
    @13
    @8
    cY
    cX
    @6
    caddc
    co
    #
    wceq
    #
    @14
    @11
    @3
    @5
    @8
    @16
    wb
    #
    @4
    @0
    @3
    @5
    @17
    @2
    @0
    @3
    @5
    w3a
    @7
    @6
    wceq
    #
    @15
    cY
    wceq
    #
    @8
    @16
    @3
    @0
    @5
    @18
    @19
    wb
    #
    @3
    cY
    cc
    wcel
    #
    @0
    cX
    cc
    wcel
    #
    @5
    @6
    cc
    wcel
    @20
    cS
    cc
    cY
    cS
    cn0
    cc
    cS
    cD
    cN
    vr
    cv
    cmin
    co
    cdvds
    wbr
    #
    vr
    cn0
    crab
    cn0
    divalglem8.4
    @23
    vr
    cn0
    ssrab2
    eqsstri
    #
    nn0sscn
    sstri
    #
    sseli
    #
    cS
    cc
    cX
    @25
    sseli
    #
    @5
    @6
    @5
    @1
    cz
    wcel
    #
    @6
    cz
    wcel
    @1
    cD
    cz
    wcel
    cD
    cc0
    wne
    @1
    cn
    wcel
    divalglem8.2
    divalglem8.3
    cD
    nnabscl
    mp2an
    #
    nnzi
    #
    cK
    @1
    zmulcl
    mpan2
    zcnd
    cY
    cX
    @6
    subadd
    syl3an
    3com12
    @7
    @6
    eqcom
    @15
    cY
    eqcom
    3bitr3g
    3adant1r
    3adant2r
    @13
    @16
    cK
    cc0
    wne
    #
    wn
    #
    @14
    @13
    @16
    @15
    cc0
    @1
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    @32
    @12
    @11
    @16
    @34
    wi
    @5
    @3
    @16
    @4
    @34
    @3
    @4
    cY
    @33
    wcel
    #
    @16
    @34
    vz
    cv
    #
    @1
    clt
    wbr
    #
    @36
    @33
    wcel
    #
    wi
    #
    @4
    @35
    wi
    vz
    cY
    cS
    @36
    cY
    wceq
    @37
    @4
    @38
    @35
    @36
    cY
    @1
    clt
    breq1
    @36
    cY
    @33
    eleq1
    imbi12d
    @36
    cS
    wcel
    #
    @37
    @38
    @40
    @37
    wa
    #
    @36
    cz
    wcel
    #
    cc0
    @36
    cle
    wbr
    #
    @37
    w3a
    #
    @38
    @41
    @42
    @43
    wa
    #
    @37
    wa
    @44
    @40
    @45
    @37
    @40
    @36
    cn0
    wcel
    @45
    cS
    cn0
    @36
    @24
    sseli
    @36
    elnn0z
    sylib
    anim1i
    @42
    @43
    @37
    df-3an
    sylibr
    cc0
    cz
    wcel
    @28
    @38
    @44
    wb
    0z
    @30
    @36
    cc0
    @1
    elfzm11
    mp2an
    sylibr
    ex
    #
    vtoclga
    @16
    @35
    @34
    cY
    @15
    @33
    eleq1
    biimpd
    sylan9
    impancom
    3ad2ant2
    @13
    @31
    @34
    @11
    @5
    @31
    @34
    wn
    wi
    #
    @12
    @11
    cX
    @33
    wcel
    #
    @5
    @47
    @0
    @2
    @48
    @39
    @2
    @48
    wi
    vz
    cX
    cS
    @36
    cX
    wceq
    @37
    @2
    @38
    @48
    @36
    cX
    @1
    clt
    breq1
    @36
    cX
    @33
    eleq1
    imbi12d
    @46
    vtoclga
    imp
    cD
    cK
    cX
    divalglem8.2
    divalglem8.3
    divalglem7
    sylan
    3adant2
    con2d
    syld
    @31
    @14
    cK
    cc0
    df-ne
    con2bii
    syl6ibr
    sylbid
    @13
    @8
    @14
    @9
    @11
    @12
    @8
    @14
    wa
    #
    @9
    wi
    #
    @5
    @0
    @3
    @50
    @2
    @4
    @49
    cc0
    @7
    wceq
    #
    @0
    @3
    wa
    #
    @9
    @14
    @8
    @51
    @14
    @6
    cc0
    @7
    @14
    @6
    cc0
    @1
    cmul
    co
    cc0
    cK
    cc0
    @1
    cmul
    oveq1
    @1
    @1
    @29
    nncni
    mul02i
    syl6eq
    eqeq1d
    biimpac
    @52
    @7
    cc0
    wceq
    #
    cY
    cX
    wceq
    #
    @51
    @9
    @3
    @21
    @22
    @53
    @54
    wb
    @0
    @26
    @27
    cY
    cX
    subeq0
    syl2anr
    @7
    cc0
    eqcom
    cY
    cX
    eqcom
    3bitr3g
    syl5ib
    ad2ant2r
    3adant3
    expd
    mpdd
    3expia
    an4s
end
