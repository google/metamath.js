include "cv.mm"
include "cblen.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c2.mm"
include "cdig.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "wa.mm"
include "wo.mm"
include "elnn0.mm"
include "cdiv.mm"
include "cmin.mm"
include "nn0sumshdiglemA.mm"
include "expimpd.mm"
include "nn0sumshdiglemB.mm"
include "nneom.mm"
include "mpjaodan.mm"
include "wb.mm"
include "eqcom.mm"
include "a1i.mm"
include "nncn.mm"
include "1cnd.mm"
include "addlsub.mm"
include "1m1e0.mm"
include "eqeq2d.mm"
include "3bitrd.mm"
include "csn.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "fzo01.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "cc.mm"
include "0cn.mm"
include "cz.mm"
include "2nn.mm"
include "0z.mm"
include "dig0.mm"
include "mp2an.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "oveq12d.mm"
include "cr.mm"
include "1re.mm"
include "mul02lem2.mm"
include "sumsn.mm"
include "syl6req.mm"
include "syl6bi.mm"
include "adantl.mm"
include "blen0.mm"
include "adantr.mm"
include "mpbird.mm"
include "a1d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ex.mm"
include "syl5bi.mm"

theorem nn0sumshdiglem1
  let vy: setvar y
  let vk: setvar k
  let va: setvar a
  let vi: setvar i
  let vx: setvar x

  disjoint a k
  disjoint a y
  disjoint k y
  disjoint a i
  disjoint a x
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k x
  disjoint x y
  disjoint k x
  assert |- ( y e. NN -> ( A. a e. NN0 ( ( #b ` a ) = y -> a = sum_ k e. ( 0 ..^ y ) ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) -> A. a e. NN0 ( ( #b ` a ) = ( y + 1 ) -> a = sum_ k e. ( 0 ..^ ( y + 1 ) ) ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) )

  proof
    va
    cv
    #
    cblen
    cfv
    #
    vy
    cv
    #
    wceq
    #
    @0
    cc0
    @2
    cfzo
    co
    #
    vk
    cv
    #
    @0
    c2
    cdig
    cfv
    #
    co
    #
    c2
    @5
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    va
    cn0
    wral
    vx
    cv
    #
    cblen
    cfv
    #
    @2
    wceq
    #
    @13
    @4
    @5
    @13
    @6
    co
    #
    @8
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @2
    cn
    wcel
    #
    @1
    @2
    c1
    caddc
    co
    #
    wceq
    #
    @0
    cc0
    @23
    cfzo
    co
    #
    @9
    vk
    csu
    #
    wceq
    #
    wi
    #
    va
    cn0
    wral
    #
    @12
    @20
    va
    vx
    cn0
    va
    vx
    weq
    #
    @3
    @15
    @11
    @19
    @30
    @1
    @14
    @2
    @0
    @13
    cblen
    fveq2
    eqeq1d
    @30
    @0
    @13
    @10
    @18
    @30
    id
    @30
    @4
    @9
    @17
    vk
    @30
    @7
    @16
    @8
    cmul
    @0
    @13
    @5
    @6
    oveq2
    oveq1d
    sumeq2sdv
    eqeq12d
    imbi12d
    cbvralv
    @22
    @21
    @29
    @22
    @21
    wa
    #
    @28
    va
    cn0
    @0
    cn0
    wcel
    #
    @31
    @28
    @32
    @0
    cn
    wcel
    #
    @0
    cc0
    wceq
    #
    wo
    @31
    @28
    wi
    #
    @0
    elnn0
    @33
    @35
    @34
    @33
    @0
    c2
    cdiv
    co
    cn
    wcel
    #
    @35
    @0
    c1
    cmin
    co
    c2
    cdiv
    co
    cn0
    wcel
    #
    @33
    @36
    wa
    @22
    @21
    @28
    vx
    vy
    vk
    va
    nn0sumshdiglemA
    expimpd
    @33
    @37
    wa
    @22
    @21
    @28
    vx
    vy
    vk
    va
    nn0sumshdiglemB
    expimpd
    @0
    nneom
    mpjaodan
    @34
    @22
    @21
    @28
    @34
    @22
    wa
    #
    @28
    @21
    @38
    @28
    c1
    @23
    wceq
    #
    cc0
    @25
    @5
    cc0
    @6
    co
    #
    @8
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    @22
    @44
    @34
    @22
    @39
    @2
    cc0
    wceq
    #
    @43
    @22
    @39
    @23
    c1
    wceq
    #
    @2
    c1
    c1
    cmin
    co
    #
    wceq
    @45
    @39
    @46
    wb
    @22
    c1
    @23
    eqcom
    a1i
    @22
    @2
    c1
    c1
    @2
    nncn
    @22
    1cnd
    #
    @48
    addlsub
    @22
    @47
    cc0
    @2
    @47
    cc0
    wceq
    @22
    1m1e0
    a1i
    eqeq2d
    3bitrd
    @45
    @42
    cc0
    csn
    #
    @41
    vk
    csu
    #
    cc0
    @45
    @25
    @49
    @41
    vk
    @45
    @25
    cc0
    cc0
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @49
    @45
    @23
    @51
    cc0
    cfzo
    @2
    cc0
    c1
    caddc
    oveq1
    oveq2d
    @52
    cc0
    c1
    cfzo
    co
    @49
    @51
    c1
    cc0
    cfzo
    0p1e1
    oveq2i
    fzo01
    eqtri
    syl6eq
    sumeq1d
    cc0
    cc
    wcel
    #
    @53
    @50
    cc0
    wceq
    0cn
    0cn
    @41
    cc0
    vk
    cc0
    cc
    @5
    cc0
    wceq
    #
    @41
    cc0
    c1
    cmul
    co
    #
    cc0
    @54
    @40
    cc0
    @8
    c1
    cmul
    @54
    @40
    cc0
    cc0
    @6
    co
    #
    cc0
    @5
    cc0
    cc0
    @6
    oveq1
    c2
    cn
    wcel
    cc0
    cz
    wcel
    @56
    cc0
    wceq
    2nn
    0z
    c2
    cc0
    dig0
    mp2an
    syl6eq
    @54
    @8
    c2
    cc0
    cexp
    co
    #
    c1
    @5
    cc0
    c2
    cexp
    oveq2
    c2
    cc
    wcel
    @57
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    syl6eq
    oveq12d
    c1
    cr
    wcel
    @55
    cc0
    wceq
    1re
    c1
    mul02lem2
    ax-mp
    syl6eq
    sumsn
    mp2an
    syl6req
    syl6bi
    adantl
    @34
    @28
    @44
    wb
    @22
    @34
    @24
    @39
    @27
    @43
    @34
    @1
    c1
    @23
    @34
    @1
    cc0
    cblen
    cfv
    c1
    @0
    cc0
    cblen
    fveq2
    blen0
    syl6eq
    eqeq1d
    @34
    @0
    cc0
    @26
    @42
    @34
    id
    @34
    @25
    @9
    @41
    vk
    @34
    @7
    @40
    @8
    cmul
    @0
    cc0
    @5
    @6
    oveq2
    oveq1d
    sumeq2sdv
    eqeq12d
    imbi12d
    adantr
    mpbird
    a1d
    expimpd
    jaoi
    sylbi
    com12
    ralrimiv
    ex
    syl5bi
end
