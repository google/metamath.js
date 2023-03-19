include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "elznn0nn.mm"
include "cc0.mm"
include "elnn0.mm"
include "c1.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "elnn1uz2.mm"
include "oveq1.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "prmz.mm"
include "zcnd.mm"
include "mulid2d.mm"
include "biimpd.mm"
include "adantl.mm"
include "sylbid.mm"
include "ex.mm"
include "wn.mm"
include "prmuz2.mm"
include "nprm.mm"
include "sylan2.mm"
include "eleq1.mm"
include "notbid.mm"
include "pm2.24.mm"
include "com12.mm"
include "syl6bi.mm"
include "com3l.mm"
include "mpcom.mm"
include "jaoi.mm"
include "sylbi.mm"
include "prmnn.mm"
include "nnred.mm"
include "mul02lem2.mm"
include "syl.mm"
include "wne.mm"
include "elnnne0.mm"
include "eqneqall.mm"
include "eqcoms.mm"
include "com23.mm"
include "clt.mm"
include "wbr.mm"
include "elnnz.mm"
include "lt0neg1.mm"
include "nngt0d.mm"
include "simpr.mm"
include "anim12ci.mm"
include "orcd.mm"
include "simprl.mm"
include "mul2lt0bi.mm"
include "mpbird.mm"
include "wb.mm"
include "breq1.mm"
include "nnnn0.mm"
include "nn0nlt0.mm"
include "pm2.21d.mm"
include "syldc.mm"
include "sylbird.mm"
include "adantld.mm"
include "syl5bi.mm"
include "imp.mm"
include "3impib.mm"

theorem ztprmneprm
  let cA: class A
  let cB: class B
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( Z e. ZZ /\ A e. Prime /\ B e. Prime ) -> ( ( Z x. A ) = B -> A = B ) )

  proof
    cZ
    cz
    wcel
    #
    cA
    cprime
    wcel
    #
    cB
    cprime
    wcel
    #
    cZ
    cA
    cmul
    co
    #
    cB
    wceq
    #
    cA
    cB
    wceq
    #
    wi
    #
    @0
    cZ
    cn0
    wcel
    #
    cZ
    cr
    wcel
    #
    cZ
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    @1
    @2
    wa
    #
    @6
    wi
    #
    cZ
    elznn0nn
    @7
    @13
    @11
    @7
    cZ
    cn
    wcel
    #
    cZ
    cc0
    wceq
    #
    wo
    @13
    cZ
    elnn0
    @14
    @13
    @15
    @14
    cZ
    c1
    wceq
    #
    cZ
    c2
    cuz
    cfv
    #
    wcel
    #
    wo
    @13
    cZ
    elnn1uz2
    @16
    @13
    @18
    @16
    @12
    @6
    @16
    @12
    wa
    #
    @4
    c1
    cA
    cmul
    co
    #
    cB
    wceq
    #
    @5
    @19
    @3
    @20
    cB
    @16
    @3
    @20
    wceq
    @12
    cZ
    c1
    cA
    cmul
    oveq1
    adantr
    eqeq1d
    @12
    @21
    @5
    wi
    @16
    @12
    @21
    @5
    @12
    @20
    cA
    cB
    @1
    @20
    cA
    wceq
    @2
    @1
    cA
    @1
    cA
    cA
    prmz
    zcnd
    mulid2d
    adantr
    eqeq1d
    biimpd
    adantl
    sylbid
    ex
    @18
    @12
    @6
    @3
    cprime
    wcel
    #
    wn
    #
    @18
    @12
    wa
    #
    @6
    @12
    @18
    cA
    @17
    wcel
    #
    @23
    @1
    @25
    @2
    cA
    prmuz2
    adantr
    cZ
    cA
    nprm
    sylan2
    @4
    @23
    @24
    @5
    @4
    @23
    @2
    wn
    #
    @24
    @5
    wi
    @4
    @22
    @2
    @3
    cB
    cprime
    eleq1
    notbid
    @24
    @26
    @5
    @12
    @26
    @5
    wi
    #
    @18
    @2
    @27
    @1
    @2
    @5
    pm2.24
    adantl
    adantl
    com12
    syl6bi
    com3l
    mpcom
    ex
    jaoi
    sylbi
    @15
    @4
    @12
    @5
    @15
    @4
    cc0
    cA
    cmul
    co
    #
    cB
    wceq
    #
    @12
    @5
    wi
    @15
    @3
    @28
    cB
    cZ
    cc0
    cA
    cmul
    oveq1
    eqeq1d
    @12
    @29
    @5
    @12
    @29
    cc0
    cB
    wceq
    #
    @5
    @12
    @28
    cc0
    cB
    @1
    @28
    cc0
    wceq
    #
    @2
    @1
    cA
    cr
    wcel
    #
    @31
    @1
    cA
    cA
    prmnn
    #
    nnred
    #
    cA
    mul02lem2
    syl
    adantr
    eqeq1d
    @2
    @30
    @5
    wi
    #
    @1
    @2
    cB
    cn
    wcel
    #
    @35
    cB
    prmnn
    #
    @36
    cB
    cn0
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    @35
    cB
    elnnne0
    @39
    @35
    @38
    @30
    @39
    @5
    @39
    @5
    wi
    cB
    cc0
    @5
    cB
    cc0
    eqneqall
    eqcoms
    com12
    adantl
    sylbi
    syl
    adantl
    sylbid
    com12
    syl6bi
    com23
    jaoi
    sylbi
    @8
    @10
    @13
    @10
    @9
    cz
    wcel
    #
    cc0
    @9
    clt
    wbr
    #
    wa
    @8
    @13
    @9
    elnnz
    @8
    @41
    @13
    @40
    @8
    @41
    cZ
    cc0
    clt
    wbr
    #
    @13
    cZ
    lt0neg1
    @8
    @42
    @13
    @12
    @8
    @42
    wa
    #
    @3
    cc0
    clt
    wbr
    #
    @6
    @12
    @43
    @44
    @12
    @43
    wa
    #
    @44
    @42
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cc0
    cZ
    clt
    wbr
    cA
    cc0
    clt
    wbr
    wa
    #
    wo
    @45
    @47
    @48
    @12
    @46
    @43
    @42
    @1
    @46
    @2
    @1
    cA
    @33
    nngt0d
    adantr
    @8
    @42
    simpr
    anim12ci
    orcd
    @45
    cZ
    cA
    @12
    @8
    @42
    simprl
    @12
    @32
    @43
    @1
    @32
    @2
    @34
    adantr
    adantr
    mul2lt0bi
    mpbird
    ex
    @12
    @4
    @44
    @5
    @12
    @4
    @44
    @5
    wi
    @12
    @4
    wa
    @44
    cB
    cc0
    clt
    wbr
    #
    @5
    @4
    @44
    @49
    wb
    @12
    @3
    cB
    cc0
    clt
    breq1
    adantl
    @12
    @49
    @5
    wi
    #
    @4
    @2
    @50
    @1
    @2
    @36
    @50
    @37
    @36
    @38
    @50
    cB
    nnnn0
    @38
    @49
    @5
    cB
    nn0nlt0
    pm2.21d
    syl
    syl
    adantl
    adantr
    sylbid
    ex
    com23
    syldc
    ex
    sylbird
    adantld
    syl5bi
    imp
    jaoi
    sylbi
    3impib
end
