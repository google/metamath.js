include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "elnn0.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "nnm1nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "wa.mm"
include "elfznn0.mm"
include "adantl.mm"
include "nn0cnd.mm"
include "id.mm"
include "fsum1p.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "sumeq1i.mm"
include "oveq2i.mm"
include "fzfid.mm"
include "elfznn.mm"
include "nncnd.mm"
include "fsumcl.mm"
include "addid2d.mm"
include "syl5eqr.mm"
include "arisum.mm"
include "syl.mm"
include "cmul.mm"
include "nncn.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "sqcld.mm"
include "subsub4d.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "cc.mm"
include "binom2sub1.mm"
include "subcld.mm"
include "1cnd.mm"
include "subsubd.mm"
include "3eqtr4d.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "npcand.mm"
include "eqtrd.mm"
include "c0.mm"
include "oveq1.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "0re.mm"
include "ltm1.mm"
include "ax-mp.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "peano2zm.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "sq0i.mm"
include "oveq12d.mm"
include "0m0e0.mm"
include "2cn.mm"
include "2ne0.mm"
include "div0i.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem arisum2
  let vk: setvar k
  let cN: class N
  let vj: setvar j

  disjoint N k
  disjoint j k
  disjoint N j
  assert |- ( N e. NN0 -> sum_ k e. ( 0 ... ( N - 1 ) ) k = ( ( ( N ^ 2 ) - N ) / 2 ) )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cc0
    cN
    c1
    cmin
    co
    #
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
    cmin
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
    @0
    @9
    @1
    @0
    @5
    cc0
    cc0
    c1
    caddc
    co
    #
    @2
    cfz
    co
    #
    @4
    vk
    csu
    #
    caddc
    co
    #
    @8
    @0
    @4
    cc0
    vk
    cc0
    @2
    @0
    @2
    cn0
    cc0
    cuz
    cfv
    cN
    nnm1nn0
    #
    nn0uz
    syl6eleq
    @0
    @4
    @3
    wcel
    #
    wa
    @4
    @15
    @4
    cn0
    wcel
    @0
    @4
    @2
    elfznn0
    adantl
    nn0cnd
    @4
    cc0
    wceq
    id
    fsum1p
    @0
    @13
    c1
    @2
    cfz
    co
    #
    @4
    vk
    csu
    #
    @8
    @0
    @13
    cc0
    @17
    caddc
    co
    @17
    @17
    @12
    cc0
    caddc
    @16
    @11
    @4
    vk
    c1
    @10
    @2
    cfz
    1e0p1
    oveq1i
    sumeq1i
    oveq2i
    @0
    @17
    @0
    @16
    @4
    vk
    @0
    c1
    @2
    fzfid
    @0
    @4
    @16
    wcel
    #
    wa
    @4
    @18
    @4
    cn
    wcel
    @0
    @4
    @2
    elfznn
    adantl
    nncnd
    fsumcl
    addid2d
    syl5eqr
    @0
    @17
    @2
    c2
    cexp
    co
    #
    @2
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @8
    @0
    @2
    cn0
    wcel
    @17
    @21
    wceq
    @14
    vk
    @2
    arisum
    syl
    @0
    @20
    @7
    c2
    cdiv
    @0
    @20
    @7
    @2
    cmin
    co
    #
    @2
    caddc
    co
    @7
    @0
    @19
    @22
    @2
    caddc
    @0
    @6
    c2
    cN
    cmul
    co
    #
    cmin
    co
    #
    c1
    caddc
    co
    #
    @7
    cN
    cmin
    co
    #
    c1
    caddc
    co
    @19
    @22
    @0
    @24
    @26
    c1
    caddc
    @0
    @24
    @6
    cN
    cN
    caddc
    co
    #
    cmin
    co
    @26
    @0
    @23
    @27
    @6
    cmin
    @0
    cN
    cN
    nncn
    #
    2timesd
    oveq2d
    @0
    @6
    cN
    cN
    @0
    cN
    @28
    sqcld
    #
    @28
    @28
    subsub4d
    eqtr4d
    oveq1d
    @0
    cN
    cc
    wcel
    #
    @19
    @25
    wceq
    @28
    cN
    binom2sub1
    syl
    @0
    @7
    cN
    c1
    @0
    @6
    cN
    @29
    @28
    subcld
    #
    @28
    @0
    1cnd
    subsubd
    3eqtr4d
    oveq1d
    @0
    @7
    @2
    @31
    @0
    @30
    c1
    cc
    wcel
    @2
    cc
    wcel
    @28
    ax-1cn
    cN
    c1
    subcl
    sylancl
    npcand
    eqtrd
    oveq1d
    eqtrd
    eqtrd
    eqtrd
    @1
    @5
    cc0
    @8
    @1
    @5
    c0
    @4
    vk
    csu
    cc0
    @1
    @3
    c0
    @4
    vk
    @1
    @3
    cc0
    cc0
    c1
    cmin
    co
    #
    cfz
    co
    #
    c0
    @1
    @2
    @32
    cc0
    cfz
    cN
    cc0
    c1
    cmin
    oveq1
    oveq2d
    @32
    cc0
    clt
    wbr
    #
    @33
    c0
    wceq
    #
    cc0
    cr
    wcel
    @34
    0re
    cc0
    ltm1
    ax-mp
    cc0
    cz
    wcel
    #
    @32
    cz
    wcel
    #
    @34
    @35
    wb
    0z
    @36
    @37
    0z
    cc0
    peano2zm
    ax-mp
    cc0
    @32
    fzn
    mp2an
    mpbi
    syl6eq
    sumeq1d
    @4
    vk
    sum0
    syl6eq
    @1
    @8
    cc0
    c2
    cdiv
    co
    cc0
    @1
    @7
    cc0
    c2
    cdiv
    @1
    @7
    cc0
    cc0
    cmin
    co
    cc0
    @1
    @6
    cc0
    cN
    cc0
    cmin
    cN
    sq0i
    @1
    id
    oveq12d
    0m0e0
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
