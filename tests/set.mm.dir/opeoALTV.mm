include "codd.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "oddz.mm"
include "evenz.mm"
include "zaddcl.mm"
include "syl2an.mm"
include "wi.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "dfodd6.mm"
include "elrab2.mm"
include "dfeven4.mm"
include "ex.mm"
include "ad3antlr.mm"
include "imp.mm"
include "adantr.mm"
include "wb.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "oveq12.mm"
include "cc.mm"
include "2cnd.mm"
include "zcn.mm"
include "mulcld.mm"
include "ancoms.mm"
include "1cnd.mm"
include "mulcl.mm"
include "add32d.mm"
include "adddid.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "r19.29an.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "sylanbrc.mm"

theorem opeoALTV
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


  assert |- ( ( A e. Odd /\ B e. Even ) -> ( A + B ) e. Odd )

  proof
    cA
    codd
    wcel
    #
    cB
    ceven
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
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @2
    codd
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
    evenz
    cA
    cB
    zaddcl
    syl2an
    @0
    @1
    @8
    @0
    @9
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
    @8
    wi
    va
    cv
    #
    @13
    wceq
    #
    vi
    cz
    wrex
    @15
    va
    cA
    cz
    codd
    @17
    cA
    wceq
    @18
    @14
    vi
    cz
    @17
    cA
    @13
    eqeq1
    rexbidv
    va
    vi
    dfodd6
    elrab2
    @1
    @10
    cB
    c2
    vj
    cv
    #
    cmul
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
    @16
    @8
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
    ceven
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
    dfeven4
    elrab2
    @9
    @14
    @23
    @8
    wi
    vi
    cz
    @9
    @11
    cz
    wcel
    #
    wa
    #
    @14
    wa
    #
    @10
    @22
    @8
    @28
    @10
    wa
    #
    @21
    @8
    vj
    cz
    @29
    @19
    cz
    wcel
    #
    wa
    #
    @21
    @8
    @31
    @21
    wa
    #
    @7
    @2
    c2
    @11
    @19
    caddc
    co
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
    vn
    @33
    cz
    @31
    @33
    cz
    wcel
    #
    @21
    @29
    @30
    @37
    @26
    @30
    @37
    wi
    @9
    @14
    @10
    @26
    @30
    @37
    @11
    @19
    zaddcl
    ex
    ad3antlr
    imp
    adantr
    @4
    @33
    wceq
    #
    @7
    @36
    wb
    @32
    @38
    @6
    @35
    @2
    @38
    @5
    @34
    c1
    caddc
    @4
    @33
    c2
    cmul
    oveq2
    oveq1d
    eqeq2d
    adantl
    @32
    @2
    @13
    @20
    caddc
    co
    #
    @35
    @31
    @21
    @2
    @39
    wceq
    #
    @14
    @21
    @40
    wi
    @27
    @10
    @30
    @14
    @21
    @40
    cA
    @13
    cB
    @20
    caddc
    oveq12
    ex
    ad3antlr
    imp
    @31
    @39
    @35
    wceq
    #
    @21
    @29
    @30
    @41
    @26
    @30
    @41
    wi
    @9
    @14
    @10
    @26
    @30
    @41
    @26
    @30
    wa
    #
    @39
    @12
    @20
    caddc
    co
    #
    c1
    caddc
    co
    @35
    @42
    @12
    c1
    @20
    @30
    @26
    @12
    cc
    wcel
    @30
    @26
    wa
    #
    c2
    @11
    @44
    2cnd
    @26
    @11
    cc
    wcel
    #
    @30
    @11
    zcn
    #
    adantl
    mulcld
    ancoms
    @42
    1cnd
    @26
    c2
    cc
    wcel
    @19
    cc
    wcel
    #
    @20
    cc
    wcel
    @30
    @26
    2cnd
    @19
    zcn
    #
    c2
    @19
    mulcl
    syl2an
    add32d
    @42
    @43
    @34
    c1
    caddc
    @42
    @34
    @43
    @42
    c2
    @11
    @19
    @42
    2cnd
    @26
    @45
    @30
    @46
    adantr
    @30
    @47
    @26
    @48
    adantl
    adddid
    eqcomd
    oveq1d
    eqtrd
    ex
    ad3antlr
    imp
    adantr
    eqtrd
    rspcedvd
    ex
    rexlimdva
    expimpd
    r19.29an
    syl5bi
    sylbi
    imp
    vz
    cv
    #
    @6
    wceq
    #
    vn
    cz
    wrex
    @8
    vz
    @2
    cz
    codd
    @49
    @2
    wceq
    @50
    @7
    vn
    cz
    @49
    @2
    @6
    eqeq1
    rexbidv
    vz
    vn
    dfodd6
    elrab2
    sylanbrc
end
