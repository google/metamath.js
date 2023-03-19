include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cbc.mm"
include "cpc.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "caddc.mm"
include "csu.mm"
include "cc0.mm"
include "wceq.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "mpan.mm"
include "adantr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "fzctr.mm"
include "syl.mm"
include "simpr.mm"
include "pcbc.mm"
include "syl3anc.mm"
include "nncn.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "ad2antrr.mm"
include "cr.mm"
include "nnre.mm"
include "prmnn.mm"
include "adantl.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "nndivred.mm"
include "flcld.mm"
include "zcnd.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"

theorem pcbcctr
  let cP: class P
  let vk: setvar k
  let cN: class N

  disjoint N k
  disjoint P k
  assert |- ( ( N e. NN /\ P e. Prime ) -> ( P pCnt ( ( 2 x. N ) _C N ) ) = sum_ k e. ( 1 ... ( 2 x. N ) ) ( ( |_ ` ( ( 2 x. N ) / ( P ^ k ) ) ) - ( 2 x. ( |_ ` ( N / ( P ^ k ) ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    #
    wa
    #
    cP
    c2
    cN
    cmul
    co
    #
    cN
    cbc
    co
    cpc
    co
    #
    c1
    @3
    cfz
    co
    #
    @3
    cP
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    cfl
    cfv
    #
    @3
    cN
    cmin
    co
    #
    @7
    cdiv
    co
    #
    cfl
    cfv
    #
    cN
    @7
    cdiv
    co
    #
    cfl
    cfv
    #
    caddc
    co
    #
    cmin
    co
    #
    vk
    csu
    #
    @5
    @8
    c2
    @13
    cmul
    co
    #
    cmin
    co
    #
    vk
    csu
    @2
    @3
    cn
    wcel
    #
    cN
    cc0
    @3
    cfz
    co
    wcel
    #
    @1
    @4
    @16
    wceq
    @0
    @19
    @1
    c2
    cn
    wcel
    @0
    @19
    2nn
    c2
    cN
    nnmulcl
    mpan
    adantr
    @0
    @20
    @1
    @0
    cN
    cn0
    wcel
    @20
    cN
    nnnn0
    cN
    fzctr
    syl
    adantr
    @0
    @1
    simpr
    cP
    vk
    cN
    @3
    pcbc
    syl3anc
    @2
    @5
    @15
    @18
    vk
    @2
    @6
    @5
    wcel
    #
    wa
    #
    @14
    @17
    @8
    cmin
    @22
    @14
    @13
    @13
    caddc
    co
    #
    @17
    @0
    @14
    @23
    wceq
    @1
    @21
    @0
    @11
    @13
    @13
    caddc
    @0
    @10
    @12
    cfl
    @0
    @9
    cN
    @7
    cdiv
    @0
    @9
    cN
    cN
    caddc
    co
    #
    cN
    cmin
    co
    cN
    @0
    @3
    @24
    cN
    cmin
    @0
    cN
    cN
    nncn
    #
    2timesd
    oveq1d
    @0
    cN
    cN
    @25
    @25
    pncand
    eqtrd
    oveq1d
    fveq2d
    oveq1d
    ad2antrr
    @22
    @13
    @22
    @13
    @22
    @12
    @22
    cN
    @7
    @0
    cN
    cr
    wcel
    @1
    @21
    cN
    nnre
    ad2antrr
    @2
    cP
    cn
    wcel
    #
    @6
    cn0
    wcel
    @7
    cn
    wcel
    @21
    @1
    @26
    @0
    cP
    prmnn
    adantl
    @21
    @6
    @6
    @3
    elfznn
    nnnn0d
    cP
    @6
    nnexpcl
    syl2an
    nndivred
    flcld
    zcnd
    2timesd
    eqtr4d
    oveq2d
    sumeq2dv
    eqtrd
end
