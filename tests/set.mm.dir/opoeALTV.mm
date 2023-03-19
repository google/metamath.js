include "codd.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "wrex.mm"
include "ceven.mm"
include "oddz.mm"
include "zaddcl.mm"
include "syl2an.mm"
include "c1.mm"
include "wi.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "dfodd6.mm"
include "elrab2.mm"
include "ex.mm"
include "ad3antlr.mm"
include "imp.mm"
include "adantr.mm"
include "peano2zd.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "oveq12.mm"
include "cc.mm"
include "zcn.mm"
include "2cnd.mm"
include "anim1i.mm"
include "ancoms.mm"
include "mulcl.mm"
include "syl.mm"
include "1cnd.mm"
include "sylan.mm"
include "add4d.mm"
include "simpl.mm"
include "simpr.mm"
include "adddid.mm"
include "oveq1d.mm"
include "addcl.mm"
include "1p1e2.mm"
include "2t1e2.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "dfeven4.mm"
include "sylanbrc.mm"

theorem opoeALTV
  let cA: class A
  let cB: class B
  let va: setvar a
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vz: setvar z
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Odd /\ B e. Odd ) -> ( A + B ) e. Even )

  proof
    cA
    codd
    wcel
    #
    cB
    codd
    wcel
    #
    wa
    cA
    cB
    caddc
    co
    #
    cz
    wcel
    #
    @2
    c2
    vn
    cv
    #
    cmul
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @2
    ceven
    wcel
    @0
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @3
    @1
    cA
    oddz
    cB
    oddz
    cA
    cB
    zaddcl
    syl2an
    @0
    @1
    @7
    @0
    @8
    cA
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
    wa
    #
    @1
    @7
    wi
    va
    cv
    #
    @12
    wceq
    #
    vi
    cz
    wrex
    @14
    va
    cA
    cz
    codd
    @16
    cA
    wceq
    @17
    @13
    vi
    cz
    @16
    cA
    @12
    eqeq1
    rexbidv
    va
    vi
    dfodd6
    elrab2
    @1
    @9
    cB
    c2
    vj
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
    vj
    cz
    wrex
    #
    wa
    #
    @15
    @7
    vb
    cv
    #
    @20
    wceq
    #
    vj
    cz
    wrex
    @22
    vb
    cB
    cz
    codd
    @24
    cB
    wceq
    @25
    @21
    vj
    cz
    @24
    cB
    @20
    eqeq1
    rexbidv
    vb
    vj
    dfodd6
    elrab2
    @8
    @14
    @23
    @7
    wi
    #
    @8
    @13
    @26
    vi
    cz
    @8
    @10
    cz
    wcel
    #
    wa
    #
    @13
    @26
    @28
    @13
    wa
    #
    @9
    @22
    @7
    @29
    @9
    wa
    #
    @21
    @7
    vj
    cz
    @30
    @18
    cz
    wcel
    #
    wa
    #
    @21
    @7
    @32
    @21
    wa
    #
    @6
    @2
    c2
    @10
    @18
    caddc
    co
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    wceq
    #
    vn
    @35
    cz
    @33
    @34
    @32
    @34
    cz
    wcel
    #
    @21
    @30
    @31
    @38
    @27
    @31
    @38
    wi
    @8
    @13
    @9
    @27
    @31
    @38
    @10
    @18
    zaddcl
    ex
    ad3antlr
    imp
    adantr
    peano2zd
    @4
    @35
    wceq
    #
    @6
    @37
    wb
    @33
    @39
    @5
    @36
    @2
    @4
    @35
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @33
    @2
    @12
    @20
    caddc
    co
    #
    @36
    @32
    @21
    @2
    @40
    wceq
    #
    @13
    @21
    @41
    wi
    @28
    @9
    @31
    @13
    @21
    @41
    cA
    @12
    cB
    @20
    caddc
    oveq12
    ex
    ad3antlr
    imp
    @32
    @40
    @36
    wceq
    #
    @21
    @30
    @31
    @42
    @27
    @31
    @42
    wi
    @8
    @13
    @9
    @27
    @31
    @42
    @27
    @10
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @42
    @31
    @10
    zcn
    @18
    zcn
    @43
    @44
    wa
    #
    @40
    @11
    @19
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @36
    @45
    @11
    c1
    @19
    c1
    @45
    c2
    cc
    wcel
    #
    @43
    wa
    #
    @11
    cc
    wcel
    @44
    @43
    @50
    @44
    @49
    @43
    @44
    2cnd
    anim1i
    ancoms
    c2
    @10
    mulcl
    syl
    @45
    1cnd
    #
    @43
    @49
    @44
    @19
    cc
    wcel
    @43
    2cnd
    c2
    @18
    mulcl
    sylan
    @51
    add4d
    @45
    c2
    @34
    cmul
    co
    #
    c2
    c1
    cmul
    co
    #
    caddc
    co
    @46
    @53
    caddc
    co
    @36
    @48
    @45
    @52
    @46
    @53
    caddc
    @45
    c2
    @10
    @18
    @45
    2cnd
    #
    @43
    @44
    simpl
    @43
    @44
    simpr
    adddid
    oveq1d
    @45
    c2
    @34
    c1
    @54
    @10
    @18
    addcl
    @51
    adddid
    @45
    @47
    @53
    @46
    caddc
    @47
    @53
    wceq
    @45
    @47
    c2
    @53
    1p1e2
    2t1e2
    eqtr4i
    a1i
    oveq2d
    3eqtr4rd
    eqtrd
    syl2an
    ex
    ad3antlr
    imp
    adantr
    eqtrd
    rspcedvd
    ex
    rexlimdva
    expimpd
    ex
    rexlimdva
    imp
    syl5bi
    sylbi
    imp
    vz
    cv
    #
    @5
    wceq
    #
    vn
    cz
    wrex
    @7
    vz
    @2
    cz
    ceven
    @55
    @2
    wceq
    @56
    @6
    vn
    cz
    @55
    @2
    @5
    eqeq1
    rexbidv
    vz
    vn
    dfeven4
    elrab2
    sylanbrc
end
