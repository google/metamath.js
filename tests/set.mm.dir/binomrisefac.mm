include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cfallfac.mm"
include "cmul.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "csu.mm"
include "crisefac.mm"
include "wceq.mm"
include "negdi.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "negcl.mm"
include "id.mm"
include "binomfallfac.mm"
include "syl3an.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fzfid.mm"
include "neg1cn.mm"
include "expcl.mm"
include "mpan.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cz.mm"
include "simp3.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2an.mm"
include "nn0cnd.mm"
include "simpl1.mm"
include "negcld.mm"
include "cle.mm"
include "wbr.mm"
include "nn0zd.mm"
include "zsubcl.mm"
include "elfzle2.mm"
include "adantl.mm"
include "simpl3.mm"
include "nn0red.mm"
include "elfznn0.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "fallfaccl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "mulcld.mm"
include "fsummulc2.mm"
include "addcl.mm"
include "risefallfac.mm"
include "stoic3.mm"
include "simpl2.mm"
include "oveq12d.mm"
include "sylancr.mm"
include "mul4d.mm"
include "a1i.mm"
include "expaddd.mm"
include "npcan.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"
include "adantr.mm"
include "mul12d.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"

theorem binomrisefac
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N

  disjoint A k
  disjoint B k
  disjoint N k
  assert |- ( ( A e. CC /\ B e. CC /\ N e. NN0 ) -> ( ( A + B ) RiseFac N ) = sum_ k e. ( 0 ... N ) ( ( N _C k ) x. ( ( A RiseFac ( N - k ) ) x. ( B RiseFac k ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    cA
    cB
    caddc
    co
    #
    cneg
    #
    cN
    cfallfac
    co
    #
    cmul
    co
    #
    cc0
    cN
    cfz
    co
    #
    @5
    cN
    vk
    cv
    #
    cbc
    co
    #
    cA
    cneg
    #
    cN
    @11
    cmin
    co
    #
    cfallfac
    co
    #
    cB
    cneg
    #
    @11
    cfallfac
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @6
    cN
    crisefac
    co
    #
    @10
    @12
    cA
    @14
    crisefac
    co
    #
    cB
    @11
    crisefac
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    @3
    @9
    @5
    @10
    @19
    vk
    csu
    #
    cmul
    co
    @21
    @3
    @8
    @27
    @5
    cmul
    @3
    @8
    @13
    @16
    caddc
    co
    #
    cN
    cfallfac
    co
    #
    @27
    @3
    @7
    @28
    cN
    cfallfac
    @0
    @1
    @7
    @28
    wceq
    @2
    cA
    cB
    negdi
    3adant3
    oveq1d
    @0
    @13
    cc
    wcel
    #
    @1
    @16
    cc
    wcel
    #
    @2
    @2
    @29
    @27
    wceq
    cA
    negcl
    cB
    negcl
    @2
    id
    @13
    @16
    vk
    cN
    binomfallfac
    syl3an
    eqtrd
    oveq2d
    @3
    @10
    @19
    @5
    vk
    @3
    cc0
    cN
    fzfid
    @2
    @0
    @5
    cc
    wcel
    #
    @1
    @4
    cc
    wcel
    #
    @2
    @32
    neg1cn
    @4
    cN
    expcl
    mpan
    3ad2ant3
    #
    @3
    @11
    @10
    wcel
    #
    wa
    #
    @12
    @18
    @36
    @12
    @3
    @2
    @11
    cz
    wcel
    #
    @12
    cn0
    wcel
    @35
    @0
    @1
    @2
    simp3
    #
    @11
    cc0
    cN
    elfzelz
    #
    @11
    cN
    bccl
    syl2an
    nn0cnd
    #
    @36
    @15
    @17
    @36
    @30
    @14
    cn0
    wcel
    #
    @15
    cc
    wcel
    @36
    cA
    @0
    @1
    @2
    @35
    simpl1
    #
    negcld
    @36
    @14
    cz
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @41
    @3
    cN
    cz
    wcel
    @37
    @43
    @35
    @3
    cN
    @38
    nn0zd
    @39
    cN
    @11
    zsubcl
    syl2an
    @36
    @44
    @11
    cN
    cle
    wbr
    #
    @35
    @45
    @3
    @11
    cc0
    cN
    elfzle2
    adantl
    @36
    cN
    @11
    @36
    cN
    @0
    @1
    @2
    @35
    simpl3
    nn0red
    @36
    @11
    @35
    @11
    cn0
    wcel
    #
    @3
    @11
    cN
    elfznn0
    #
    adantl
    #
    nn0red
    subge0d
    mpbird
    @14
    elnn0z
    sylanbrc
    #
    @13
    @14
    fallfaccl
    syl2anc
    #
    @3
    @31
    @46
    @17
    cc
    wcel
    @35
    @3
    cB
    @0
    @1
    @2
    simp2
    negcld
    @47
    @16
    @11
    fallfaccl
    syl2an
    #
    mulcld
    #
    mulcld
    fsummulc2
    eqtrd
    @0
    @1
    @6
    cc
    wcel
    @2
    @22
    @9
    wceq
    cA
    cB
    addcl
    cN
    @6
    risefallfac
    stoic3
    @3
    @10
    @26
    @20
    vk
    @36
    @26
    @12
    @5
    @18
    cmul
    co
    #
    cmul
    co
    @20
    @36
    @25
    @53
    @12
    cmul
    @36
    @25
    @4
    @14
    cexp
    co
    #
    @15
    cmul
    co
    #
    @4
    @11
    cexp
    co
    #
    @17
    cmul
    co
    #
    cmul
    co
    @54
    @56
    cmul
    co
    #
    @18
    cmul
    co
    @53
    @36
    @23
    @55
    @24
    @57
    cmul
    @36
    @0
    @41
    @23
    @55
    wceq
    @42
    @49
    @14
    cA
    risefallfac
    syl2anc
    @36
    @1
    @46
    @24
    @57
    wceq
    @0
    @1
    @2
    @35
    simpl2
    @48
    @11
    cB
    risefallfac
    syl2anc
    oveq12d
    @36
    @54
    @15
    @56
    @17
    @36
    @33
    @41
    @54
    cc
    wcel
    neg1cn
    @49
    @4
    @14
    expcl
    sylancr
    @50
    @35
    @56
    cc
    wcel
    #
    @3
    @35
    @33
    @46
    @59
    neg1cn
    @47
    @4
    @11
    expcl
    sylancr
    adantl
    @51
    mul4d
    @36
    @58
    @5
    @18
    cmul
    @36
    @4
    @14
    @11
    caddc
    co
    #
    cexp
    co
    @58
    @5
    @36
    @4
    @14
    @11
    @33
    @36
    neg1cn
    a1i
    @48
    @49
    expaddd
    @36
    @60
    cN
    @4
    cexp
    @3
    cN
    cc
    wcel
    @11
    cc
    wcel
    @60
    cN
    wceq
    @35
    @3
    cN
    @38
    nn0cnd
    @35
    @11
    @47
    nn0cnd
    cN
    @11
    npcan
    syl2an
    oveq2d
    eqtr3d
    oveq1d
    3eqtrd
    oveq2d
    @36
    @12
    @5
    @18
    @40
    @3
    @32
    @35
    @34
    adantr
    @52
    mul12d
    eqtrd
    sumeq2dv
    3eqtr4d
end
