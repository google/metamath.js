include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "wceq.mm"
include "1cnd.mm"
include "negid.mm"
include "eqcomd.mm"
include "syl.mm"
include "oveq1d.mm"
include "0exp.mm"
include "cmin.mm"
include "cn0.mm"
include "negcld.mm"
include "nnnn0.mm"
include "binom.mm"
include "syl3anc.mm"
include "wa.mm"
include "cz.mm"
include "nnz.mm"
include "elfzelz.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "1exp.mm"
include "neg1cn.mm"
include "a1i.mm"
include "elfznn0.mm"
include "expcl.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "bccl.mm"
include "nn0cnd.mm"
include "mulcomd.mm"
include "sumeq2dv.mm"
include "3eqtr3rd.mm"

theorem altgsumbc
  let vk: setvar k
  let cN: class N
  let vx: setvar x

  disjoint N k
  disjoint k x
  assert |- ( N e. NN -> sum_ k e. ( 0 ... N ) ( ( -u 1 ^ k ) x. ( N _C k ) ) = 0 )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    cexp
    co
    c1
    c1
    cneg
    #
    caddc
    co
    #
    cN
    cexp
    co
    #
    cc0
    cc0
    cN
    cfz
    co
    #
    @1
    vk
    cv
    #
    cexp
    co
    #
    cN
    @5
    cbc
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @0
    cc0
    @2
    cN
    cexp
    @0
    c1
    cc
    wcel
    #
    cc0
    @2
    wceq
    @0
    1cnd
    #
    @10
    @2
    cc0
    c1
    negid
    eqcomd
    syl
    oveq1d
    cN
    0exp
    @0
    @3
    @4
    @7
    c1
    cN
    @5
    cmin
    co
    #
    cexp
    co
    #
    @6
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @9
    @0
    @10
    @1
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    @3
    @16
    wceq
    @11
    @0
    c1
    @11
    negcld
    cN
    nnnn0
    #
    c1
    @1
    vk
    cN
    binom
    syl3anc
    @0
    @4
    @15
    @8
    vk
    @0
    @5
    @4
    wcel
    #
    wa
    #
    @15
    @7
    @6
    cmul
    co
    @8
    @21
    @14
    @6
    @7
    cmul
    @21
    @14
    c1
    @6
    cmul
    co
    @6
    @21
    @13
    c1
    @6
    cmul
    @21
    @12
    cz
    wcel
    #
    @13
    c1
    wceq
    @0
    cN
    cz
    wcel
    @5
    cz
    wcel
    #
    @22
    @20
    cN
    nnz
    @5
    cc0
    cN
    elfzelz
    #
    cN
    @5
    zsubcl
    syl2an
    @12
    1exp
    syl
    oveq1d
    @21
    @6
    @0
    @17
    @5
    cn0
    wcel
    @6
    cc
    wcel
    @20
    @17
    @0
    neg1cn
    a1i
    @5
    cN
    elfznn0
    @1
    @5
    expcl
    syl2an
    #
    mulid2d
    eqtrd
    oveq2d
    @21
    @7
    @6
    @21
    @7
    @0
    @18
    @23
    @7
    cn0
    wcel
    @20
    @19
    @24
    @5
    cN
    bccl
    syl2an
    nn0cnd
    @25
    mulcomd
    eqtrd
    sumeq2dv
    eqtrd
    3eqtr3rd
end
