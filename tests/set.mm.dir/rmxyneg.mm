include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cneg.mm"
include "crmx.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "crmy.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "znegcl.mm"
include "rmxyval.mm"
include "sylan2.mm"
include "cdiv.mm"
include "oveq2d.mm"
include "cc.mm"
include "rmbaserp.mm"
include "rpcnd.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0d.mm"
include "simpr.mm"
include "expclzd.mm"
include "eqeltrd.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "cn.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "nncnd.mm"
include "sqrtcld.mm"
include "frmy.mm"
include "zcnd.mm"
include "negcld.mm"
include "mulcld.mm"
include "addcld.mm"
include "expne0d.mm"
include "eqnetrd.mm"
include "mulneg2d.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "subsq.mm"
include "syl2anc.mm"
include "sqmuld.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "rmxynorm.mm"
include "3eqtr2d.mm"
include "mvllmuld.mm"
include "expnegd.mm"
include "3eqtr4rd.mm"
include "cq.mm"
include "cdif.mm"
include "wb.mm"
include "rmspecsqrtnq.mm"
include "nn0ssq.mm"
include "sseldi.mm"
include "zssq.mm"
include "qnegcl.mm"
include "syl.mm"
include "qirropth.mm"
include "syl122anc.mm"
include "mpbid.mm"

theorem rmxyneg
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A rmX -u N ) = ( A rmX N ) /\ ( A rmY -u N ) = -u ( A rmY N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    cneg
    #
    crmx
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cA
    @4
    crmy
    co
    #
    cmul
    co
    caddc
    co
    #
    cA
    cN
    crmx
    co
    #
    @7
    cA
    cN
    crmy
    co
    #
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @5
    @10
    wceq
    @8
    @12
    wceq
    wa
    #
    @3
    @9
    cA
    @7
    caddc
    co
    #
    @4
    cexp
    co
    #
    @14
    @2
    @1
    @4
    cz
    wcel
    #
    @9
    @18
    wceq
    cN
    znegcl
    #
    cA
    @4
    rmxyval
    sylan2
    @3
    c1
    @10
    @7
    @11
    cmul
    co
    #
    caddc
    co
    #
    cdiv
    co
    c1
    @17
    cN
    cexp
    co
    #
    cdiv
    co
    @14
    @18
    @3
    @22
    @23
    c1
    cdiv
    cA
    cN
    rmxyval
    #
    oveq2d
    @3
    @22
    @14
    c1
    @3
    @22
    @23
    cc
    @24
    @3
    @17
    cN
    @1
    @17
    cc
    wcel
    @2
    @1
    @17
    cA
    rmbaserp
    #
    rpcnd
    adantr
    #
    @1
    @17
    cc0
    wne
    @2
    @1
    @17
    @25
    rpne0d
    adantr
    #
    @1
    @2
    simpr
    #
    expclzd
    eqeltrd
    @3
    @10
    @13
    @3
    @10
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    #
    nn0cnd
    #
    @3
    @7
    @12
    @3
    @6
    @1
    @6
    cc
    wcel
    @2
    @1
    @6
    @1
    @6
    cn
    csquarenn
    cA
    rmspecnonsq
    eldifad
    nncnd
    adantr
    #
    sqrtcld
    #
    @3
    @11
    @3
    @11
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    #
    zcnd
    #
    negcld
    mulcld
    addcld
    @3
    @22
    @23
    cc0
    @24
    @3
    @17
    cN
    @26
    @27
    @28
    expne0d
    eqnetrd
    @3
    @22
    @14
    cmul
    co
    @22
    @10
    @21
    cmin
    co
    #
    cmul
    co
    #
    @10
    c2
    cexp
    co
    #
    @21
    c2
    cexp
    co
    #
    cmin
    co
    #
    c1
    @3
    @14
    @35
    @22
    cmul
    @3
    @14
    @10
    @21
    cneg
    #
    caddc
    co
    @35
    @3
    @13
    @40
    @10
    caddc
    @3
    @7
    @11
    @32
    @34
    mulneg2d
    oveq2d
    @3
    @10
    @21
    @30
    @3
    @7
    @11
    @32
    @34
    mulcld
    #
    negsubd
    eqtrd
    oveq2d
    @3
    @10
    cc
    wcel
    @21
    cc
    wcel
    @39
    @36
    wceq
    @30
    @41
    @10
    @21
    subsq
    syl2anc
    @3
    @39
    @37
    @6
    @11
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    c1
    @3
    @38
    @43
    @37
    cmin
    @3
    @38
    @7
    c2
    cexp
    co
    #
    @42
    cmul
    co
    @43
    @3
    @7
    @11
    @32
    @34
    sqmuld
    @3
    @44
    @6
    @42
    cmul
    @3
    @6
    @31
    sqsqrtd
    oveq1d
    eqtrd
    oveq2d
    cA
    cN
    rmxynorm
    eqtrd
    3eqtr2d
    mvllmuld
    @3
    @17
    cN
    @26
    @27
    @28
    expnegd
    3eqtr4rd
    eqtrd
    @3
    @7
    cc
    cq
    cdif
    wcel
    #
    @5
    cq
    wcel
    @8
    cq
    wcel
    @10
    cq
    wcel
    @12
    cq
    wcel
    #
    @15
    @16
    wb
    @1
    @45
    @2
    cA
    rmspecsqrtnq
    adantr
    @3
    cn0
    cq
    @5
    nn0ssq
    @2
    @1
    @19
    @5
    cn0
    wcel
    @20
    cA
    @4
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    sseldi
    @3
    cz
    cq
    @8
    zssq
    @2
    @1
    @19
    @8
    cz
    wcel
    @20
    cA
    @4
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    sseldi
    @3
    cn0
    cq
    @10
    nn0ssq
    @29
    sseldi
    @3
    @11
    cq
    wcel
    @46
    @3
    cz
    cq
    @11
    zssq
    @33
    sseldi
    @11
    qnegcl
    syl
    @7
    @5
    @8
    @10
    @12
    qirropth
    syl122anc
    mpbid
end
