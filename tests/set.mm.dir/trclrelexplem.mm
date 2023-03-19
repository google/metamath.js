include "cn.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "wss.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "iuneq2d.mm"
include "sseq12d.mm"
include "weq.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "relexp1g.mm"
include "mp1i.mm"
include "iuneq2i.mm"
include "nnex.mm"
include "iunex.mm"
include "ax-mp.mm"
include "3eqtr4i.mm"
include "eqimssi.mm"
include "wa.mm"
include "ccom.mm"
include "oveq1d.mm"
include "coeq12d.mm"
include "ss2iun.mm"
include "ssiun2s.mm"
include "coss1.mm"
include "syl.mm"
include "mprg.mm"
include "eqsstri.mm"
include "wral.mm"
include "ralrimivw.mm"
include "syl5ss.mm"
include "adantl.mm"
include "relexpsucnnr.mm"
include "mpan.mm"
include "adantr.mm"
include "coeq2i.mm"
include "coiun.mm"
include "syl6eq.mm"
include "3sstr4d.mm"
include "ex.mm"
include "nnind.mm"

theorem trclrelexplem
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vl: setvar l
  let vm: setvar m

  disjoint D j
  disjoint D k
  disjoint N k
  disjoint D x
  disjoint D y
  disjoint j x
  disjoint j y
  disjoint x y
  disjoint k x
  disjoint k y
  disjoint D l
  disjoint D m
  disjoint N x
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint m y
  assert |- ( N e. NN -> U_ k e. NN ( ( D ^r k ) ^r N ) C_ ( U_ j e. NN ( D ^r j ) ^r N ) )

  proof
    vk
    cn
    cD
    vk
    cv
    #
    crelexp
    co
    #
    vx
    cv
    #
    crelexp
    co
    #
    ciun
    #
    vj
    cn
    cD
    vj
    cv
    #
    crelexp
    co
    #
    ciun
    #
    @2
    crelexp
    co
    #
    wss
    vk
    cn
    @1
    c1
    crelexp
    co
    #
    ciun
    #
    @7
    c1
    crelexp
    co
    #
    wss
    vk
    cn
    @1
    vy
    cv
    #
    crelexp
    co
    #
    ciun
    #
    @7
    @12
    crelexp
    co
    #
    wss
    #
    vk
    cn
    @1
    @12
    c1
    caddc
    co
    #
    crelexp
    co
    #
    ciun
    #
    @7
    @17
    crelexp
    co
    #
    wss
    #
    vk
    cn
    @1
    cN
    crelexp
    co
    #
    ciun
    #
    @7
    cN
    crelexp
    co
    #
    wss
    vx
    vy
    cN
    @2
    c1
    wceq
    #
    @4
    @10
    @8
    @11
    @25
    vk
    cn
    @3
    @9
    @2
    c1
    @1
    crelexp
    oveq2
    iuneq2d
    @2
    c1
    @7
    crelexp
    oveq2
    sseq12d
    vx
    vy
    weq
    #
    @4
    @14
    @8
    @15
    @26
    vk
    cn
    @3
    @13
    @2
    @12
    @1
    crelexp
    oveq2
    iuneq2d
    @2
    @12
    @7
    crelexp
    oveq2
    sseq12d
    @2
    @17
    wceq
    #
    @4
    @19
    @8
    @20
    @27
    vk
    cn
    @3
    @18
    @2
    @17
    @1
    crelexp
    oveq2
    iuneq2d
    @2
    @17
    @7
    crelexp
    oveq2
    sseq12d
    @2
    cN
    wceq
    #
    @4
    @23
    @8
    @24
    @28
    vk
    cn
    @3
    @22
    @2
    cN
    @1
    crelexp
    oveq2
    iuneq2d
    @2
    cN
    @7
    crelexp
    oveq2
    sseq12d
    @10
    @11
    vk
    cn
    @1
    ciun
    #
    @7
    @10
    @11
    @29
    vl
    cn
    cD
    vl
    cv
    #
    crelexp
    co
    #
    ciun
    @7
    vk
    vl
    cn
    @1
    @31
    @0
    @30
    cD
    crelexp
    oveq2
    cbviunv
    vl
    vj
    cn
    @31
    @6
    @30
    @5
    cD
    crelexp
    oveq2
    cbviunv
    eqtri
    vk
    cn
    @9
    @1
    @1
    cvv
    wcel
    #
    @9
    @1
    wceq
    @0
    cn
    wcel
    cD
    @0
    crelexp
    ovex
    #
    @1
    cvv
    relexp1g
    mp1i
    iuneq2i
    @7
    cvv
    wcel
    #
    @11
    @7
    wceq
    vj
    cn
    @6
    nnex
    cD
    @5
    crelexp
    ovex
    iunex
    #
    @7
    cvv
    relexp1g
    ax-mp
    3eqtr4i
    eqimssi
    @12
    cn
    wcel
    #
    @16
    @21
    @36
    @16
    wa
    vk
    cn
    @13
    @1
    ccom
    #
    ciun
    #
    vm
    cn
    @15
    cD
    vm
    cv
    #
    crelexp
    co
    #
    ccom
    #
    ciun
    #
    @19
    @20
    @16
    @38
    @42
    wss
    @36
    @16
    @38
    vm
    cn
    @14
    @40
    ccom
    #
    ciun
    #
    @42
    @38
    vm
    cn
    @40
    @12
    crelexp
    co
    #
    @40
    ccom
    #
    ciun
    #
    @44
    vk
    vm
    cn
    @37
    @46
    vk
    vm
    weq
    #
    @13
    @45
    @1
    @40
    @48
    @1
    @40
    @12
    crelexp
    @0
    @39
    cD
    crelexp
    oveq2
    #
    oveq1d
    #
    @49
    coeq12d
    cbviunv
    @46
    @43
    wss
    #
    @47
    @44
    wss
    vm
    cn
    vm
    cn
    @46
    @43
    ss2iun
    @39
    cn
    wcel
    @45
    @14
    wss
    @51
    vk
    cn
    @13
    @39
    @45
    @50
    ssiun2s
    @45
    @14
    @40
    coss1
    syl
    mprg
    eqsstri
    @16
    @43
    @41
    wss
    #
    vm
    cn
    wral
    @44
    @42
    wss
    @16
    @52
    vm
    cn
    @14
    @15
    @40
    coss1
    ralrimivw
    vm
    cn
    @43
    @41
    ss2iun
    syl
    syl5ss
    adantl
    @36
    @19
    @38
    wceq
    @16
    @36
    vk
    cn
    @18
    @37
    @32
    @36
    @18
    @37
    wceq
    @33
    @1
    @12
    cvv
    relexpsucnnr
    mpan
    iuneq2d
    adantr
    @36
    @20
    @42
    wceq
    @16
    @36
    @20
    @15
    @7
    ccom
    #
    @42
    @34
    @36
    @20
    @53
    wceq
    @35
    @7
    @12
    cvv
    relexpsucnnr
    mpan
    @53
    @15
    vm
    cn
    @40
    ciun
    #
    ccom
    @42
    @7
    @54
    @15
    vj
    vm
    cn
    @6
    @40
    @5
    @39
    cD
    crelexp
    oveq2
    cbviunv
    coeq2i
    vm
    @15
    @40
    cn
    coiun
    eqtri
    syl6eq
    adantr
    3sstr4d
    ex
    nnind
end
