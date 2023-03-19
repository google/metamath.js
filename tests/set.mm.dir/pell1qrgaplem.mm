include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "wceq.mm"
include "crp.mm"
include "nnrp.mm"
include "ad2antrr.mm"
include "1rp.mm"
include "a1i.mm"
include "rpaddcld.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "cr.mm"
include "nn0re.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "remulcld.mm"
include "cle.mm"
include "cc0.mm"
include "1re.mm"
include "resqcld.mm"
include "resubcld.mm"
include "0red.mm"
include "sq1.mm"
include "nnge1.mm"
include "wn.mm"
include "simplrl.mm"
include "oveq1.mm"
include "sq0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cc.mm"
include "rpcnd.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "recnd.mm"
include "sqcld.mm"
include "subid1d.mm"
include "3eqtr3d.mm"
include "syl5req.mm"
include "wb.mm"
include "nn0ge0.mm"
include "0le1.mm"
include "sq11.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "simpr.mm"
include "oveq12d.mm"
include "1p0e1.mm"
include "breqtrd.mm"
include "ltnri.mm"
include "pm2.24.mm"
include "mpisyl.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "le2sqd.mm"
include "eqbrtrrd.mm"
include "suble0d.mm"
include "mpbird.mm"
include "lemul2d.mm"
include "leadd2dd.mm"
include "sqsqrtd.mm"
include "simprr.mm"
include "eqcomd.mm"
include "mulcld.mm"
include "addsub12d.mm"
include "subdid.mm"
include "mulid1d.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "addid1d.mm"
include "3brtr4d.mm"
include "rpge0d.mm"
include "le2addd.mm"

theorem pell1qrgaplem
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( D e. NN /\ ( A e. NN0 /\ B e. NN0 ) ) /\ ( 1 < ( A + ( ( sqrt ` D ) x. B ) ) /\ ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) = 1 ) ) -> ( ( sqrt ` ( D + 1 ) ) + ( sqrt ` D ) ) <_ ( A + ( ( sqrt ` D ) x. B ) ) )

  proof
    cD
    cn
    wcel
    #
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    wa
    #
    c1
    cA
    cD
    csqrt
    cfv
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    cA
    c2
    cexp
    co
    #
    cD
    cB
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    wa
    #
    cD
    c1
    caddc
    co
    #
    csqrt
    cfv
    #
    @5
    cA
    @6
    @15
    @17
    @15
    @16
    @15
    cD
    c1
    @0
    cD
    crp
    wcel
    @3
    @14
    cD
    nnrp
    ad2antrr
    #
    c1
    crp
    wcel
    @15
    1rp
    a1i
    rpaddcld
    #
    rpsqrtcld
    #
    rpred
    #
    @15
    @5
    @15
    cD
    @18
    rpsqrtcld
    #
    rpred
    #
    @3
    cA
    cr
    wcel
    #
    @0
    @14
    @1
    @24
    @2
    cA
    nn0re
    adantr
    ad2antlr
    #
    @15
    @5
    cB
    @23
    @3
    cB
    cr
    wcel
    #
    @0
    @14
    @2
    @26
    @1
    cB
    nn0re
    adantl
    ad2antlr
    #
    remulcld
    @15
    @17
    cA
    cle
    wbr
    @17
    c2
    cexp
    co
    #
    @9
    cle
    wbr
    @15
    @9
    cD
    c1
    @10
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @9
    cD
    cc0
    cmul
    co
    #
    caddc
    co
    #
    @28
    @9
    cle
    @15
    @30
    @32
    @9
    @15
    cD
    @29
    @15
    cD
    @18
    rpred
    #
    @15
    c1
    @10
    c1
    cr
    wcel
    #
    @15
    1re
    a1i
    #
    @15
    cB
    @27
    resqcld
    #
    resubcld
    #
    remulcld
    @15
    cD
    cc0
    @34
    @15
    0red
    #
    remulcld
    @15
    cA
    @25
    resqcld
    @15
    @29
    cc0
    cle
    wbr
    #
    @30
    @32
    cle
    wbr
    @15
    @40
    c1
    @10
    cle
    wbr
    @15
    c1
    c2
    cexp
    co
    #
    c1
    @10
    cle
    @41
    c1
    wceq
    @15
    sq1
    a1i
    @15
    c1
    cB
    cle
    wbr
    #
    @41
    @10
    cle
    wbr
    @15
    cB
    cn
    wcel
    #
    @42
    cB
    cc0
    wceq
    #
    @43
    @42
    @15
    cB
    nnge1
    adantl
    @15
    @44
    wa
    #
    c1
    c1
    clt
    wbr
    #
    @46
    wn
    @42
    @45
    c1
    @7
    c1
    clt
    @4
    @8
    @13
    @44
    simplrl
    @45
    @7
    c1
    cc0
    caddc
    co
    c1
    @45
    cA
    c1
    @6
    cc0
    caddc
    @45
    @9
    @41
    wceq
    #
    cA
    c1
    wceq
    #
    @45
    @41
    c1
    @9
    sq1
    @45
    @12
    @9
    cc0
    cmin
    co
    c1
    @9
    @45
    @11
    cc0
    @9
    cmin
    @45
    @11
    @32
    cc0
    @45
    @10
    cc0
    cD
    cmul
    @45
    @10
    cc0
    c2
    cexp
    co
    #
    cc0
    @44
    @10
    @49
    wceq
    @15
    cB
    cc0
    c2
    cexp
    oveq1
    adantl
    sq0
    syl6eq
    oveq2d
    @45
    cD
    @15
    cD
    cc
    wcel
    @44
    @15
    cD
    @18
    rpcnd
    #
    adantr
    mul01d
    eqtrd
    oveq2d
    @4
    @8
    @13
    @44
    simplrr
    @45
    @9
    @15
    @9
    cc
    wcel
    @44
    @15
    cA
    @15
    cA
    @25
    recnd
    sqcld
    #
    adantr
    subid1d
    3eqtr3d
    syl5req
    @15
    @47
    @48
    wb
    #
    @44
    @15
    @24
    cc0
    cA
    cle
    wbr
    #
    @35
    cc0
    c1
    cle
    wbr
    #
    @52
    @25
    @3
    @53
    @0
    @14
    @1
    @53
    @2
    cA
    nn0ge0
    adantr
    ad2antlr
    #
    @36
    @54
    @15
    0le1
    a1i
    #
    cA
    c1
    sq11
    syl22anc
    adantr
    mpbid
    @45
    @6
    @5
    cc0
    cmul
    co
    cc0
    @45
    cB
    cc0
    @5
    cmul
    @15
    @44
    simpr
    oveq2d
    @45
    @5
    @15
    @5
    cc
    wcel
    @44
    @15
    @5
    @22
    rpcnd
    #
    adantr
    mul01d
    eqtrd
    oveq12d
    1p0e1
    syl6eq
    breqtrd
    c1
    1re
    ltnri
    @46
    @42
    pm2.24
    mpisyl
    @15
    @2
    @43
    @44
    wo
    @0
    @1
    @2
    @14
    simplrr
    cB
    elnn0
    sylib
    mpjaodan
    #
    @15
    c1
    cB
    @36
    @27
    @56
    @3
    cc0
    cB
    cle
    wbr
    #
    @0
    @14
    @2
    @59
    @1
    cB
    nn0ge0
    adantl
    ad2antlr
    le2sqd
    mpbid
    eqbrtrrd
    @15
    c1
    @10
    @36
    @37
    suble0d
    mpbird
    @15
    @29
    cc0
    cD
    @38
    @39
    @18
    lemul2d
    mpbid
    leadd2dd
    @15
    @28
    @16
    cD
    @12
    caddc
    co
    #
    @31
    @15
    @16
    @15
    @16
    @19
    rpcnd
    sqsqrtd
    @15
    c1
    @12
    cD
    caddc
    @15
    @12
    c1
    @4
    @8
    @13
    simprr
    eqcomd
    oveq2d
    @15
    @60
    @9
    cD
    @11
    cmin
    co
    #
    caddc
    co
    @31
    @15
    cD
    @9
    @11
    @50
    @51
    @15
    cD
    @10
    @50
    @15
    cB
    @15
    cB
    @27
    recnd
    sqcld
    #
    mulcld
    addsub12d
    @15
    @61
    @30
    @9
    caddc
    @15
    @30
    cD
    c1
    cmul
    co
    #
    @11
    cmin
    co
    @61
    @15
    cD
    c1
    @10
    @50
    @15
    c1
    @36
    recnd
    @62
    subdid
    @15
    @63
    cD
    @11
    cmin
    @15
    cD
    @50
    mulid1d
    oveq1d
    eqtr2d
    oveq2d
    eqtrd
    3eqtrd
    @15
    @33
    @9
    cc0
    caddc
    co
    @9
    @15
    @32
    cc0
    @9
    caddc
    @15
    cD
    @50
    mul01d
    oveq2d
    @15
    @9
    @51
    addid1d
    eqtr2d
    3brtr4d
    @15
    @17
    cA
    @21
    @25
    @15
    @17
    @20
    rpge0d
    @55
    le2sqd
    mpbird
    @15
    @5
    c1
    cmul
    co
    #
    @5
    @6
    cle
    @15
    @5
    @57
    mulid1d
    @15
    @42
    @64
    @6
    cle
    wbr
    @58
    @15
    c1
    cB
    @5
    @36
    @27
    @22
    lemul2d
    mpbid
    eqbrtrrd
    le2addd
end
