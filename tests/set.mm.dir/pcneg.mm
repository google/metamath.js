include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cneg.mm"
include "cpc.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cdiv.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "elq.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "nncn.mm"
include "ad2antll.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divnegd.mm"
include "oveq2d.mm"
include "neg0.mm"
include "simpr.mm"
include "negeqd.mm"
include "3eqtr4a.mm"
include "oveq1d.mm"
include "cmin.mm"
include "simpll.mm"
include "simplrl.mm"
include "znegcld.mm"
include "wb.mm"
include "negne0bd.mm"
include "syl.mm"
include "mpbid.mm"
include "simplrr.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "pczpre.mm"
include "syl12anc.mm"
include "prmz.mm"
include "zexpcl.mm"
include "sylan.mm"
include "simpl.mm"
include "dvdsnegb.mm"
include "syl2an.mm"
include "an32s.mm"
include "rabbidva.mm"
include "supeq1d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "pm2.61dane.mm"
include "negeq.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "imp.mm"

theorem pcneg
  let cA: class A
  let cP: class P
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( P e. Prime /\ A e. QQ ) -> ( P pCnt -u A ) = ( P pCnt A ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cq
    wcel
    #
    cP
    cA
    cneg
    #
    cpc
    co
    #
    cP
    cA
    cpc
    co
    #
    wceq
    #
    @1
    cA
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    @0
    @5
    vx
    vy
    cA
    elq
    @0
    @9
    @5
    vx
    vy
    cz
    cn
    @0
    @6
    cz
    wcel
    #
    @7
    cn
    wcel
    #
    wa
    #
    wa
    #
    @5
    @9
    cP
    @8
    cneg
    #
    cpc
    co
    #
    cP
    @8
    cpc
    co
    #
    wceq
    @13
    @15
    cP
    @6
    cneg
    #
    @7
    cdiv
    co
    #
    cpc
    co
    #
    @16
    @13
    @14
    @18
    cP
    cpc
    @13
    @6
    @7
    @10
    @6
    cc
    wcel
    @0
    @11
    @6
    zcn
    #
    ad2antrl
    @11
    @7
    cc
    wcel
    @0
    @10
    @7
    nncn
    ad2antll
    @11
    @7
    cc0
    wne
    @0
    @10
    @7
    nnne0
    ad2antll
    divnegd
    oveq2d
    @13
    @19
    @16
    wceq
    @6
    cc0
    @13
    @6
    cc0
    wceq
    #
    wa
    #
    @18
    @8
    cP
    cpc
    @22
    @17
    @6
    @7
    cdiv
    @22
    cc0
    cneg
    cc0
    @17
    @6
    neg0
    @22
    @6
    cc0
    @13
    @21
    simpr
    #
    negeqd
    @23
    3eqtr4a
    oveq1d
    oveq2d
    @13
    @6
    cc0
    wne
    #
    wa
    #
    @19
    cP
    @17
    cpc
    co
    #
    cP
    @7
    cpc
    co
    #
    cmin
    co
    #
    @16
    @25
    @0
    @17
    cz
    wcel
    #
    @17
    cc0
    wne
    #
    @11
    @19
    @28
    wceq
    @0
    @12
    @24
    simpll
    #
    @25
    @6
    @0
    @10
    @11
    @24
    simplrl
    #
    znegcld
    #
    @25
    @24
    @30
    @13
    @24
    simpr
    #
    @25
    @10
    @24
    @30
    wb
    @32
    @10
    @6
    @20
    negne0bd
    syl
    mpbid
    #
    @0
    @10
    @11
    @24
    simplrr
    #
    @17
    @7
    cP
    pcdiv
    syl121anc
    @25
    @16
    cP
    @6
    cpc
    co
    #
    @27
    cmin
    co
    #
    @28
    @25
    @0
    @10
    @24
    @11
    @16
    @38
    wceq
    @31
    @32
    @34
    @36
    @6
    @7
    cP
    pcdiv
    syl121anc
    @25
    @26
    @37
    @27
    cmin
    @25
    @26
    cP
    @7
    cexp
    co
    #
    @17
    cdvds
    wbr
    #
    vy
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @37
    @25
    @0
    @29
    @30
    @26
    @42
    wceq
    @31
    @33
    @35
    cP
    @42
    vy
    @17
    @42
    eqid
    pczpre
    syl12anc
    @25
    @0
    @10
    @24
    @37
    @42
    wceq
    @31
    @32
    @34
    @0
    @10
    @24
    wa
    #
    wa
    #
    @37
    @39
    @6
    cdvds
    wbr
    #
    vy
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @42
    cP
    @47
    vy
    @6
    @47
    eqid
    pczpre
    @44
    cr
    @46
    @41
    clt
    @44
    @45
    @40
    vy
    cn0
    @0
    @7
    cn0
    wcel
    #
    @43
    @45
    @40
    wb
    #
    @0
    @48
    wa
    @39
    cz
    wcel
    #
    @10
    @49
    @43
    @0
    cP
    cz
    wcel
    @48
    @50
    cP
    prmz
    cP
    @7
    zexpcl
    sylan
    @10
    @24
    simpl
    @39
    @6
    dvdsnegb
    syl2an
    an32s
    rabbidva
    supeq1d
    eqtrd
    syl12anc
    eqtr4d
    oveq1d
    eqtr4d
    eqtr4d
    pm2.61dane
    eqtrd
    @9
    @3
    @15
    @4
    @16
    @9
    @2
    @14
    cP
    cpc
    cA
    @8
    negeq
    oveq2d
    cA
    @8
    cP
    cpc
    oveq2
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bi
    imp
end
