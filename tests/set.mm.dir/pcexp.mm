include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "cpc.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "pc1.mm"
include "adantr.mm"
include "cc.mm"
include "qcn.mm"
include "ad2antrl.mm"
include "exp0d.mm"
include "pcqcl.mm"
include "zcnd.mm"
include "mul02d.mm"
include "3eqtr4d.mm"
include "cn0.mm"
include "wi.mm"
include "expp1.mm"
include "sylan.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "nn0z.mm"
include "adantl.mm"
include "qexpclz.mm"
include "syl3anc.mm"
include "expne0d.mm"
include "pcqmul.mm"
include "syl122anc.mm"
include "eqtrd.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "adddird.mm"
include "mulid2d.mm"
include "syl5ibr.mm"
include "ex.mm"
include "cn.mm"
include "negeq.mm"
include "cdiv.mm"
include "nnnn0.mm"
include "expneg.mm"
include "syl2an.mm"
include "sylan2.mm"
include "pcrec.mm"
include "syl12anc.mm"
include "nncn.mm"
include "mulneg1.mm"
include "syl2anr.mm"
include "zindd.mm"
include "3impia.mm"

theorem pcexp
  let cA: class A
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ ( A e. QQ /\ A =/= 0 ) /\ N e. ZZ ) -> ( P pCnt ( A ^ N ) ) = ( N x. ( P pCnt A ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cq
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cN
    cz
    wcel
    cP
    cA
    cN
    cexp
    co
    #
    cpc
    co
    #
    cN
    cP
    cA
    cpc
    co
    #
    cmul
    co
    #
    wceq
    #
    cP
    cA
    vx
    cv
    #
    cexp
    co
    #
    cpc
    co
    #
    @9
    @6
    cmul
    co
    #
    wceq
    cP
    cA
    cc0
    cexp
    co
    #
    cpc
    co
    #
    cc0
    @6
    cmul
    co
    #
    wceq
    cP
    cA
    vy
    cv
    #
    cexp
    co
    #
    cpc
    co
    #
    @16
    @6
    cmul
    co
    #
    wceq
    #
    cP
    cA
    @16
    cneg
    #
    cexp
    co
    #
    cpc
    co
    #
    @21
    @6
    cmul
    co
    #
    wceq
    #
    cP
    cA
    @16
    c1
    caddc
    co
    #
    cexp
    co
    #
    cpc
    co
    #
    @26
    @6
    cmul
    co
    #
    wceq
    #
    @8
    @0
    @3
    wa
    #
    vx
    vy
    cN
    @9
    cc0
    wceq
    #
    @11
    @14
    @12
    @15
    @32
    @10
    @13
    cP
    cpc
    @9
    cc0
    cA
    cexp
    oveq2
    oveq2d
    @9
    cc0
    @6
    cmul
    oveq1
    eqeq12d
    @9
    @16
    wceq
    #
    @11
    @18
    @12
    @19
    @33
    @10
    @17
    cP
    cpc
    @9
    @16
    cA
    cexp
    oveq2
    oveq2d
    @9
    @16
    @6
    cmul
    oveq1
    eqeq12d
    @9
    @26
    wceq
    #
    @11
    @28
    @12
    @29
    @34
    @10
    @27
    cP
    cpc
    @9
    @26
    cA
    cexp
    oveq2
    oveq2d
    @9
    @26
    @6
    cmul
    oveq1
    eqeq12d
    @9
    @21
    wceq
    #
    @11
    @23
    @12
    @24
    @35
    @10
    @22
    cP
    cpc
    @9
    @21
    cA
    cexp
    oveq2
    oveq2d
    @9
    @21
    @6
    cmul
    oveq1
    eqeq12d
    @9
    cN
    wceq
    #
    @11
    @5
    @12
    @7
    @36
    @10
    @4
    cP
    cpc
    @9
    cN
    cA
    cexp
    oveq2
    oveq2d
    @9
    cN
    @6
    cmul
    oveq1
    eqeq12d
    @31
    cP
    c1
    cpc
    co
    #
    cc0
    @14
    @15
    @0
    @37
    cc0
    wceq
    @3
    cP
    pc1
    adantr
    @31
    @13
    c1
    cP
    cpc
    @31
    cA
    @1
    cA
    cc
    wcel
    #
    @0
    @2
    cA
    qcn
    ad2antrl
    #
    exp0d
    oveq2d
    @31
    @6
    @31
    @6
    cP
    cA
    pcqcl
    zcnd
    #
    mul02d
    3eqtr4d
    @31
    @16
    cn0
    wcel
    #
    @20
    @30
    wi
    @20
    @30
    @31
    @41
    wa
    #
    @18
    @6
    caddc
    co
    #
    @19
    @6
    caddc
    co
    #
    wceq
    @18
    @19
    @6
    caddc
    oveq1
    @42
    @28
    @43
    @29
    @44
    @42
    @28
    cP
    @17
    cA
    cmul
    co
    #
    cpc
    co
    #
    @43
    @42
    @27
    @45
    cP
    cpc
    @31
    @38
    @41
    @27
    @45
    wceq
    @39
    cA
    @16
    expp1
    sylan
    oveq2d
    @42
    @0
    @17
    cq
    wcel
    #
    @17
    cc0
    wne
    #
    @1
    @2
    @46
    @43
    wceq
    @0
    @3
    @41
    simpll
    @42
    @1
    @2
    @16
    cz
    wcel
    #
    @47
    @0
    @1
    @2
    @41
    simplrl
    #
    @0
    @1
    @2
    @41
    simplrr
    #
    @41
    @49
    @31
    @16
    nn0z
    adantl
    #
    cA
    @16
    qexpclz
    syl3anc
    #
    @42
    cA
    @16
    @31
    @38
    @41
    @39
    adantr
    @51
    @52
    expne0d
    #
    @50
    @51
    @17
    cA
    cP
    pcqmul
    syl122anc
    eqtrd
    @42
    @29
    @19
    c1
    @6
    cmul
    co
    #
    caddc
    co
    @44
    @42
    @16
    c1
    @6
    @41
    @16
    cc
    wcel
    #
    @31
    @16
    nn0cn
    adantl
    @42
    1cnd
    @31
    @6
    cc
    wcel
    #
    @41
    @40
    adantr
    #
    adddird
    @42
    @55
    @6
    @19
    caddc
    @42
    @6
    @58
    mulid2d
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    ex
    @31
    @16
    cn
    wcel
    #
    @20
    @25
    wi
    @20
    @25
    @31
    @59
    wa
    #
    @18
    cneg
    #
    @19
    cneg
    #
    wceq
    @18
    @19
    negeq
    @60
    @23
    @61
    @24
    @62
    @60
    @23
    cP
    c1
    @17
    cdiv
    co
    #
    cpc
    co
    #
    @61
    @60
    @22
    @63
    cP
    cpc
    @31
    @38
    @41
    @22
    @63
    wceq
    @59
    @39
    @16
    nnnn0
    #
    cA
    @16
    expneg
    syl2an
    oveq2d
    @60
    @0
    @47
    @48
    @64
    @61
    wceq
    @0
    @3
    @59
    simpll
    @59
    @31
    @41
    @47
    @65
    @53
    sylan2
    @59
    @31
    @41
    @48
    @65
    @54
    sylan2
    @17
    cP
    pcrec
    syl12anc
    eqtrd
    @59
    @56
    @57
    @24
    @62
    wceq
    @31
    @16
    nncn
    @40
    @16
    @6
    mulneg1
    syl2anr
    eqeq12d
    syl5ibr
    ex
    zindd
    3impia
end
