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
include "c1.mm"
include "csn.mm"
include "caddc.mm"
include "eqeq2.mm"
include "oveq2.mm"
include "fzo01.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "weq.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "0cnd.mm"
include "cn.mm"
include "cz.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "a1i.mm"
include "0zd.mm"
include "nn0rp0.mm"
include "digvalnn0.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "mulcld.mm"
include "jca.mm"
include "adantr.mm"
include "oveq1.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "oveq12d.mm"
include "sumsn.mm"
include "syl.mm"
include "mulid1d.mm"
include "cpr.mm"
include "wo.mm"
include "blen1b.mm"
include "biimpa.mm"
include "vex.mm"
include "elpr.mm"
include "sylibr.mm"
include "0dig2pr01.mm"
include "3eqtrrd.mm"
include "ex.mm"
include "rgen.mm"
include "nn0sumshdiglem1.mm"
include "nnind.mm"

theorem nn0sumshdiglem2
  let vk: setvar k
  let cL: class L
  let va: setvar a
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y

  disjoint a k
  disjoint L a
  disjoint L k
  disjoint a i
  disjoint a x
  disjoint a y
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint L x
  disjoint L y
  disjoint k x
  assert |- ( L e. NN -> A. a e. NN0 ( ( #b ` a ) = L -> a = sum_ k e. ( 0 ..^ L ) ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) )

  proof
    va
    cv
    #
    cblen
    cfv
    #
    vx
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
    @1
    c1
    wceq
    #
    @0
    cc0
    csn
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
    @1
    vy
    cv
    #
    wceq
    #
    @0
    cc0
    @18
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
    @1
    @18
    c1
    caddc
    co
    #
    wceq
    #
    @0
    cc0
    @24
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
    @1
    cL
    wceq
    #
    @0
    cc0
    cL
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
    vx
    vy
    cL
    @2
    c1
    wceq
    #
    @12
    @17
    va
    cn0
    @35
    @3
    @13
    @11
    @16
    @2
    c1
    @1
    eqeq2
    @35
    @10
    @15
    @0
    @35
    @4
    @14
    @9
    vk
    @35
    @4
    cc0
    c1
    cfzo
    co
    @14
    @2
    c1
    cc0
    cfzo
    oveq2
    fzo01
    syl6eq
    sumeq1d
    eqeq2d
    imbi12d
    ralbidv
    vx
    vy
    weq
    #
    @12
    @23
    va
    cn0
    @36
    @3
    @19
    @11
    @22
    @2
    @18
    @1
    eqeq2
    @36
    @10
    @21
    @0
    @36
    @4
    @20
    @9
    vk
    @2
    @18
    cc0
    cfzo
    oveq2
    sumeq1d
    eqeq2d
    imbi12d
    ralbidv
    @2
    @24
    wceq
    #
    @12
    @29
    va
    cn0
    @37
    @3
    @25
    @11
    @28
    @2
    @24
    @1
    eqeq2
    @37
    @10
    @27
    @0
    @37
    @4
    @26
    @9
    vk
    @2
    @24
    cc0
    cfzo
    oveq2
    sumeq1d
    eqeq2d
    imbi12d
    ralbidv
    @2
    cL
    wceq
    #
    @12
    @34
    va
    cn0
    @38
    @3
    @30
    @11
    @33
    @2
    cL
    @1
    eqeq2
    @38
    @10
    @32
    @0
    @38
    @4
    @31
    @9
    vk
    @2
    cL
    cc0
    cfzo
    oveq2
    sumeq1d
    eqeq2d
    imbi12d
    ralbidv
    @17
    va
    cn0
    @0
    cn0
    wcel
    #
    @13
    @16
    @39
    @13
    wa
    #
    @15
    cc0
    @0
    @6
    co
    #
    c1
    cmul
    co
    #
    @41
    @0
    @40
    cc0
    cc
    wcel
    #
    @42
    cc
    wcel
    #
    wa
    #
    @15
    @42
    wceq
    @39
    @45
    @13
    @39
    @43
    @44
    @39
    0cnd
    @39
    @41
    c1
    @39
    @41
    @39
    c2
    cn
    wcel
    #
    cc0
    cz
    wcel
    @0
    cc0
    cpnf
    cico
    co
    wcel
    @41
    cn0
    wcel
    @46
    @39
    2nn
    a1i
    @39
    0zd
    @0
    nn0rp0
    c2
    @0
    cc0
    digvalnn0
    syl3anc
    nn0cnd
    #
    @39
    1cnd
    mulcld
    jca
    adantr
    @9
    @42
    vk
    cc0
    cc
    @5
    cc0
    wceq
    #
    @7
    @41
    @8
    c1
    cmul
    @5
    cc0
    @0
    @6
    oveq1
    @48
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
    @49
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    syl6eq
    oveq12d
    sumsn
    syl
    @40
    @41
    @39
    @41
    cc
    wcel
    @13
    @47
    adantr
    mulid1d
    @40
    @0
    cc0
    c1
    cpr
    wcel
    #
    @41
    @0
    wceq
    @40
    @0
    cc0
    wceq
    @0
    c1
    wceq
    wo
    #
    @50
    @39
    @13
    @51
    @0
    blen1b
    biimpa
    @0
    cc0
    c1
    va
    vex
    elpr
    sylibr
    @0
    0dig2pr01
    syl
    3eqtrrd
    ex
    rgen
    vy
    vk
    va
    nn0sumshdiglem1
    nnind
end
