include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "cz.mm"
include "c2.mm"
include "cmul.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "wi.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "zaddcl.mm"
include "ancoms.mm"
include "adantr.mm"
include "simpl.mm"
include "syl2anr.mm"
include "wb.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "simpr.mm"
include "oveqan12rd.mm"
include "2cnd.mm"
include "cc.mm"
include "zcn.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "eqeq1d.mm"
include "mpbird.mm"
include "ex.mm"
include "rexlimdvaa.mm"
include "rexlimiva.mm"
include "imp.mm"
include "syl6ibr.mm"
include "impcom.mm"
include "sylanbrc.mm"
include "exp32.mm"
include "impancom.mm"
include "com13.mm"
include "sylbi.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "cc0.mm"
include "crab.mm"
include "0z.mm"
include "2cn.mm"
include "0zd.mm"
include "mul01.mm"
include "eqcomd.mm"
include "ax-mp.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "eleqtrri.mm"
include "2zrngbas.mm"
include "2zrngadd.mm"
include "ismgmn0.mm"
include "mpbir.mm"

theorem 2zrngamgm
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )

  disjoint x z
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint x y
  disjoint y z
  disjoint k x
  assert |- R e. Mgm

  proof
    cR
    cmgm
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    caddc
    co
    #
    cE
    wcel
    #
    vb
    cE
    wral
    va
    cE
    wral
    #
    @4
    va
    vb
    cE
    @1
    cE
    wcel
    @1
    cz
    wcel
    #
    @1
    c2
    vx
    cv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    @2
    cz
    wcel
    #
    @2
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    @4
    @2
    cE
    wcel
    vz
    cv
    #
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    @10
    vz
    @1
    cz
    cE
    @16
    @1
    wceq
    @17
    @9
    vx
    cz
    @16
    @1
    @8
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @18
    @14
    vz
    @2
    cz
    cE
    @16
    @2
    wceq
    @17
    @13
    vx
    cz
    @16
    @2
    @8
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @11
    @15
    @4
    @10
    @6
    @15
    @4
    wi
    #
    @10
    @1
    c2
    vy
    cv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cz
    wrex
    #
    @6
    @19
    wi
    @9
    @22
    vx
    vy
    cz
    @7
    @20
    wceq
    @8
    @21
    @1
    @7
    @20
    c2
    cmul
    oveq2
    eqeq2d
    cbvrexv
    @15
    @6
    @23
    @4
    @12
    @6
    @14
    @23
    @4
    wi
    @12
    @6
    wa
    #
    @14
    @23
    @4
    @24
    @14
    @23
    wa
    #
    wa
    @3
    cz
    wcel
    #
    @3
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    @4
    @24
    @26
    @25
    @6
    @12
    @26
    @1
    @2
    zaddcl
    ancoms
    adantr
    @25
    @24
    @28
    @25
    @24
    @3
    c2
    @16
    cmul
    co
    #
    wceq
    #
    vz
    cz
    wrex
    #
    @28
    @14
    @23
    @24
    @31
    wi
    #
    @13
    @23
    @32
    wi
    vx
    cz
    @7
    cz
    wcel
    #
    @13
    wa
    #
    @22
    @32
    vy
    cz
    @34
    @20
    cz
    wcel
    #
    @22
    wa
    #
    wa
    #
    @24
    @31
    @37
    @24
    wa
    #
    @31
    c2
    @20
    @7
    caddc
    co
    #
    cmul
    co
    #
    @29
    wceq
    #
    vz
    cz
    wrex
    @38
    @41
    @40
    @40
    wceq
    #
    vz
    @39
    cz
    @37
    @39
    cz
    wcel
    #
    @24
    @36
    @35
    @33
    @43
    @34
    @35
    @22
    simpl
    @33
    @13
    simpl
    @20
    @7
    zaddcl
    syl2anr
    adantr
    @16
    @39
    wceq
    #
    @41
    @42
    wb
    @38
    @44
    @29
    @40
    @40
    @16
    @39
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @38
    @40
    eqidd
    rspcedvd
    @38
    @30
    @41
    vz
    cz
    @38
    @3
    @40
    @29
    @38
    @3
    @21
    @8
    caddc
    co
    #
    @40
    @37
    @3
    @45
    wceq
    @24
    @36
    @34
    @1
    @21
    @2
    @8
    caddc
    @35
    @22
    simpr
    @33
    @13
    simpr
    oveqan12rd
    adantr
    @37
    @40
    @45
    wceq
    @24
    @37
    c2
    @20
    @7
    @37
    2cnd
    @36
    @20
    cc
    wcel
    #
    @34
    @35
    @46
    @22
    @20
    zcn
    adantr
    adantl
    @34
    @7
    cc
    wcel
    #
    @36
    @33
    @47
    @13
    @7
    zcn
    adantr
    adantr
    adddid
    adantr
    eqtr4d
    eqeq1d
    rexbidv
    mpbird
    ex
    rexlimdvaa
    rexlimiva
    imp
    @27
    @30
    vx
    vz
    cz
    @7
    @16
    wceq
    @8
    @29
    @3
    @7
    @16
    c2
    cmul
    oveq2
    eqeq2d
    cbvrexv
    syl6ibr
    impcom
    @18
    @28
    vz
    @3
    cz
    cE
    @16
    @3
    wceq
    @17
    @27
    vx
    cz
    @16
    @3
    @8
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    sylanbrc
    exp32
    impancom
    com13
    sylbi
    impcom
    imp
    syl2anb
    rgen2a
    cc0
    cE
    wcel
    @0
    @5
    wb
    cc0
    @18
    vz
    cz
    crab
    #
    cE
    cc0
    @48
    wcel
    cc0
    cz
    wcel
    cc0
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    0z
    c2
    cc
    wcel
    #
    @50
    2cn
    @51
    @49
    cc0
    c2
    cc0
    cmul
    co
    #
    wceq
    #
    vx
    cc0
    cz
    @51
    0zd
    @7
    cc0
    wceq
    #
    @49
    @53
    wb
    @51
    @54
    @8
    @52
    cc0
    @7
    cc0
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @51
    @52
    cc0
    c2
    mul01
    eqcomd
    rspcedvd
    ax-mp
    @18
    @50
    vz
    cc0
    cz
    @16
    cc0
    wceq
    @17
    @49
    vx
    cz
    @16
    cc0
    @8
    eqeq1
    rexbidv
    elrab
    mpbir2an
    2zrng.e
    eleqtrri
    va
    vb
    cc0
    cE
    cR
    caddc
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngadd
    ismgmn0
    ax-mp
    mpbir
end
