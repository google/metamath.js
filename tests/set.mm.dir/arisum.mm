include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cdiv.mm"
include "elnn0.mm"
include "cmin.mm"
include "cbc.mm"
include "1zzd.mm"
include "nnz.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "id.mm"
include "fsumshftm.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "sumeq1i.mm"
include "syl6eq.mm"
include "wa.mm"
include "elfznn0.mm"
include "bcnp1n.mm"
include "syl.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "sumeq2dv.mm"
include "1nn0.mm"
include "nnm1nn0.mm"
include "bcxmas.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "cmul.mm"
include "1cnd.mm"
include "nncn.mm"
include "ppncand.mm"
include "eqtrd.mm"
include "nnnn0.mm"
include "bcp1m1.mm"
include "adddird.mm"
include "sqval.mm"
include "eqcomd.mm"
include "mulid2.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "c0.mm"
include "oveq2.mm"
include "fz10.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "sq0i.mm"
include "00id.mm"
include "2cn.mm"
include "2ne0.mm"
include "div0i.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem arisum
  let vk: setvar k
  let cN: class N
  let vj: setvar j

  disjoint N k
  disjoint j k
  disjoint N j
  assert |- ( N e. NN0 -> sum_ k e. ( 1 ... N ) k = ( ( ( N ^ 2 ) + N ) / 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    vk
    csu
    #
    cN
    c2
    cexp
    co
    #
    cN
    caddc
    co
    #
    c2
    cdiv
    co
    #
    wceq
    #
    cN
    elnn0
    @1
    @9
    @2
    @1
    @5
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    vj
    cv
    #
    c1
    caddc
    co
    #
    vj
    csu
    #
    c1
    c1
    caddc
    co
    @10
    caddc
    co
    #
    @10
    cbc
    co
    #
    @8
    @1
    @5
    c1
    c1
    cmin
    co
    #
    @10
    cfz
    co
    #
    @13
    vj
    csu
    @14
    @1
    @4
    @13
    vk
    vj
    c1
    c1
    cN
    @1
    1zzd
    #
    @19
    cN
    nnz
    @4
    @3
    wcel
    #
    @4
    cc
    wcel
    @1
    @20
    @4
    @4
    c1
    cN
    elfzelz
    zcnd
    adantl
    @4
    @13
    wceq
    id
    fsumshftm
    @18
    @11
    @13
    vj
    @17
    cc0
    @10
    cfz
    1m1e0
    oveq1i
    sumeq1i
    syl6eq
    @1
    @14
    @11
    c1
    @12
    caddc
    co
    #
    @12
    cbc
    co
    #
    vj
    csu
    #
    @16
    @1
    @11
    @13
    @22
    vj
    @1
    @12
    @11
    wcel
    #
    wa
    #
    @13
    @12
    cbc
    co
    #
    @13
    @22
    @25
    @12
    cn0
    wcel
    #
    @26
    @13
    wceq
    @24
    @27
    @1
    @12
    @10
    elfznn0
    adantl
    #
    @12
    bcnp1n
    syl
    @25
    @13
    @21
    @12
    cbc
    @25
    @12
    cc
    wcel
    c1
    cc
    wcel
    #
    @13
    @21
    wceq
    @25
    @12
    @28
    nn0cnd
    ax-1cn
    @12
    c1
    addcom
    sylancl
    oveq1d
    eqtr3d
    sumeq2dv
    @1
    c1
    cn0
    wcel
    @10
    cn0
    wcel
    @16
    @23
    wceq
    1nn0
    cN
    nnm1nn0
    vj
    @10
    c1
    bcxmas
    sylancr
    eqtr4d
    @1
    @16
    cN
    c1
    caddc
    co
    #
    @10
    cbc
    co
    #
    @30
    cN
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @8
    @1
    @15
    @30
    @10
    cbc
    @1
    @15
    c1
    cN
    caddc
    co
    #
    @30
    @1
    c1
    c1
    cN
    @1
    1cnd
    #
    @35
    cN
    nncn
    #
    ppncand
    @1
    @29
    cN
    cc
    wcel
    #
    @34
    @30
    wceq
    ax-1cn
    @36
    c1
    cN
    addcom
    sylancr
    eqtrd
    oveq1d
    @1
    @0
    @31
    @33
    wceq
    cN
    nnnn0
    cN
    bcp1m1
    syl
    @1
    @32
    @7
    c2
    cdiv
    @1
    @32
    cN
    cN
    cmul
    co
    #
    c1
    cN
    cmul
    co
    #
    caddc
    co
    #
    @7
    @1
    cN
    c1
    cN
    @36
    @35
    @36
    adddird
    @1
    @37
    @40
    @7
    wceq
    @36
    @37
    @38
    @6
    @39
    cN
    caddc
    @37
    @6
    @38
    cN
    sqval
    eqcomd
    cN
    mulid2
    oveq12d
    syl
    eqtrd
    oveq1d
    3eqtrd
    3eqtrd
    @2
    @5
    cc0
    @8
    @2
    @5
    c0
    @4
    vk
    csu
    cc0
    @2
    @3
    c0
    @4
    vk
    @2
    @3
    c1
    cc0
    cfz
    co
    c0
    cN
    cc0
    c1
    cfz
    oveq2
    fz10
    syl6eq
    sumeq1d
    @4
    vk
    sum0
    syl6eq
    @2
    @8
    cc0
    c2
    cdiv
    co
    cc0
    @2
    @7
    cc0
    c2
    cdiv
    @2
    @7
    cc0
    cc0
    caddc
    co
    cc0
    @2
    @6
    cc0
    cN
    cc0
    caddc
    cN
    sq0i
    @2
    id
    oveq12d
    00id
    syl6eq
    oveq1d
    c2
    2cn
    2ne0
    div0i
    syl6eq
    eqtr4d
    jaoi
    sylbi
end
