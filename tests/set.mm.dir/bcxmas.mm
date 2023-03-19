include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cbc.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "wi.mm"
include "bcxmaslem1.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "0nn0.mm"
include "wa.mm"
include "nn0addcl.mm"
include "bcn0.mm"
include "syl.mm"
include "mpan2.mm"
include "cz.mm"
include "cc.mm"
include "0z.mm"
include "1nn0.mm"
include "syl6eqel.mm"
include "nn0cnd.mm"
include "fsum1.mm"
include "sylancr.mm"
include "peano2nn0.mm"
include "sylancl.mm"
include "3eqtr4rd.mm"
include "cuz.mm"
include "cfv.mm"
include "simpr.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "simpl.mm"
include "elfznn0.mm"
include "syl2an.mm"
include "elfzelz.mm"
include "adantl.mm"
include "bccl.mm"
include "syl2anc.mm"
include "fsump1.mm"
include "nn0cn.mm"
include "adantr.mm"
include "1cnd.mm"
include "add32r.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "cmin.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylan.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "nnzd.mm"
include "bcpasc.mm"
include "eqtr3d.mm"
include "nnnn0addcl.mm"
include "nnnn0d.mm"
include "nn0z.mm"
include "addcomd.mm"
include "peano2cn.mm"
include "addassd.mm"
include "3eqtr3d.mm"
include "3eqtr2rd.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem bcxmas
  let vj: setvar j
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vk: setvar k

  disjoint M j
  disjoint N j
  disjoint j m
  disjoint M m
  disjoint j k
  disjoint k m
  disjoint N k
  disjoint N m
  assert |- ( ( N e. NN0 /\ M e. NN0 ) -> ( ( ( N + 1 ) + M ) _C M ) = sum_ j e. ( 0 ... M ) ( ( N + j ) _C j ) )

  proof
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cM
    caddc
    co
    cM
    cbc
    co
    #
    cc0
    cM
    cfz
    co
    #
    cN
    vj
    cv
    #
    caddc
    co
    #
    @4
    cbc
    co
    #
    vj
    csu
    #
    wceq
    #
    @0
    @1
    vm
    cv
    #
    caddc
    co
    @9
    cbc
    co
    #
    cc0
    @9
    cfz
    co
    #
    @6
    vj
    csu
    #
    wceq
    #
    wi
    @0
    @1
    cc0
    caddc
    co
    #
    cc0
    cbc
    co
    #
    cc0
    cc0
    cfz
    co
    #
    @6
    vj
    csu
    #
    wceq
    #
    wi
    @0
    @1
    vk
    cv
    #
    caddc
    co
    #
    @19
    cbc
    co
    #
    cc0
    @19
    cfz
    co
    #
    @6
    vj
    csu
    #
    wceq
    #
    wi
    @0
    @1
    @19
    c1
    caddc
    co
    #
    caddc
    co
    #
    @25
    cbc
    co
    #
    cc0
    @25
    cfz
    co
    #
    @6
    vj
    csu
    #
    wceq
    #
    wi
    @0
    @8
    wi
    vm
    vk
    cM
    @9
    cc0
    wceq
    #
    @13
    @18
    @0
    @31
    @10
    @15
    @12
    @17
    @9
    cc0
    @1
    bcxmaslem1
    @31
    @11
    @16
    @6
    vj
    @9
    cc0
    cc0
    cfz
    oveq2
    sumeq1d
    eqeq12d
    imbi2d
    @9
    @19
    wceq
    #
    @13
    @24
    @0
    @32
    @10
    @21
    @12
    @23
    @9
    @19
    @1
    bcxmaslem1
    @32
    @11
    @22
    @6
    vj
    @9
    @19
    cc0
    cfz
    oveq2
    sumeq1d
    eqeq12d
    imbi2d
    @9
    @25
    wceq
    #
    @13
    @30
    @0
    @33
    @10
    @27
    @12
    @29
    @9
    @25
    @1
    bcxmaslem1
    @33
    @11
    @28
    @6
    vj
    @9
    @25
    cc0
    cfz
    oveq2
    sumeq1d
    eqeq12d
    imbi2d
    @9
    cM
    wceq
    #
    @13
    @8
    @0
    @34
    @10
    @2
    @12
    @7
    @9
    cM
    @1
    bcxmaslem1
    @34
    @11
    @3
    @6
    vj
    @9
    cM
    cc0
    cfz
    oveq2
    sumeq1d
    eqeq12d
    imbi2d
    @0
    cN
    cc0
    caddc
    co
    #
    cc0
    cbc
    co
    #
    c1
    @17
    @15
    @0
    cc0
    cn0
    wcel
    #
    @36
    c1
    wceq
    #
    0nn0
    @0
    @37
    wa
    @35
    cn0
    wcel
    @38
    cN
    cc0
    nn0addcl
    @35
    bcn0
    syl
    mpan2
    #
    @0
    cc0
    cz
    wcel
    @36
    cc
    wcel
    @17
    @36
    wceq
    0z
    @0
    @36
    @0
    @36
    c1
    cn0
    @39
    1nn0
    syl6eqel
    nn0cnd
    @6
    @36
    vj
    cc0
    @4
    cc0
    cN
    bcxmaslem1
    fsum1
    sylancr
    @0
    @14
    cn0
    wcel
    #
    @15
    c1
    wceq
    @0
    @1
    cn0
    wcel
    #
    @37
    @40
    cN
    peano2nn0
    #
    0nn0
    @1
    cc0
    nn0addcl
    sylancl
    @14
    bcn0
    syl
    3eqtr4rd
    @19
    cn0
    wcel
    #
    @0
    @24
    @30
    @0
    @43
    @24
    @30
    wi
    @0
    @43
    wa
    #
    @24
    @30
    @44
    @24
    wa
    @29
    @23
    @20
    @25
    cbc
    co
    #
    caddc
    co
    #
    @21
    @45
    caddc
    co
    #
    @27
    @44
    @29
    @46
    wceq
    @24
    @44
    @29
    @23
    cN
    @25
    caddc
    co
    #
    @25
    cbc
    co
    #
    caddc
    co
    @46
    @44
    @6
    @49
    vj
    cc0
    @19
    @44
    @43
    @19
    cc0
    cuz
    cfv
    wcel
    @0
    @43
    simpr
    @19
    elnn0uz
    sylib
    @44
    @4
    @28
    wcel
    #
    wa
    #
    @6
    @51
    @5
    cn0
    wcel
    #
    @4
    cz
    wcel
    #
    @6
    cn0
    wcel
    @44
    @0
    @4
    cn0
    wcel
    @52
    @50
    @0
    @43
    simpl
    @4
    @25
    elfznn0
    cN
    @4
    nn0addcl
    syl2an
    @50
    @53
    @44
    @4
    cc0
    @25
    elfzelz
    adantl
    @4
    @5
    bccl
    syl2anc
    nn0cnd
    @4
    @25
    cN
    bcxmaslem1
    fsump1
    @44
    @49
    @45
    @23
    caddc
    @44
    @48
    @20
    @25
    cbc
    @44
    cN
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @48
    @20
    wceq
    @0
    @54
    @43
    cN
    nn0cn
    #
    adantr
    @43
    @55
    @0
    @19
    nn0cn
    adantl
    #
    @44
    1cnd
    #
    cN
    @19
    c1
    add32r
    syl3anc
    oveq1d
    oveq2d
    eqtrd
    adantr
    @24
    @47
    @46
    wceq
    @44
    @21
    @23
    @45
    caddc
    oveq1
    adantl
    @44
    @47
    @27
    wceq
    @24
    @44
    @45
    @21
    caddc
    co
    #
    @20
    c1
    caddc
    co
    #
    @25
    cbc
    co
    #
    @47
    @27
    @44
    @45
    @20
    @25
    c1
    cmin
    co
    #
    cbc
    co
    #
    caddc
    co
    #
    @60
    @62
    @44
    @64
    @21
    @45
    caddc
    @44
    @63
    @19
    @20
    cbc
    @44
    @55
    @56
    @63
    @19
    wceq
    @58
    ax-1cn
    @19
    c1
    pncan
    sylancl
    oveq2d
    oveq2d
    @44
    @20
    cn0
    wcel
    #
    @25
    cz
    wcel
    #
    @65
    @62
    wceq
    @0
    @41
    @43
    @66
    @42
    @1
    @19
    nn0addcl
    #
    sylan
    @44
    @25
    @43
    @25
    cn
    wcel
    @0
    @19
    nn0p1nn
    adantl
    nnzd
    #
    @25
    @20
    bcpasc
    syl2anc
    eqtr3d
    @44
    @45
    @21
    @44
    @45
    @44
    @66
    @67
    @45
    cn0
    wcel
    @44
    @20
    @0
    @1
    cn
    wcel
    @43
    @20
    cn
    wcel
    cN
    nn0p1nn
    @1
    @19
    nnnn0addcl
    sylan
    nnnn0d
    @69
    @25
    @20
    bccl
    syl2anc
    nn0cnd
    @44
    @21
    @0
    @41
    @43
    @21
    cn0
    wcel
    #
    @42
    @41
    @43
    wa
    @66
    @19
    cz
    wcel
    #
    @70
    @68
    @43
    @71
    @41
    @19
    nn0z
    adantl
    @19
    @20
    bccl
    syl2anc
    sylan
    nn0cnd
    addcomd
    @44
    @61
    @26
    @25
    cbc
    @44
    @1
    @19
    c1
    @0
    @1
    cc
    wcel
    #
    @43
    @0
    @54
    @72
    @57
    cN
    peano2cn
    syl
    adantr
    @58
    @59
    addassd
    oveq1d
    3eqtr3d
    adantr
    3eqtr2rd
    ex
    expcom
    a2d
    nn0ind
    impcom
end
