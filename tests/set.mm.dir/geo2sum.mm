include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "csu.mm"
include "cmin.mm"
include "caddc.mm"
include "cc0.mm"
include "cmul.mm"
include "1zzd.mm"
include "cz.mm"
include "nnz.mm"
include "adantr.mm"
include "simplr.mm"
include "cn0.mm"
include "2nn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fsumshftm.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "sumeq1i.mm"
include "halfcn.mm"
include "elfznn0.mm"
include "expcl.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divrecd.mm"
include "expp1.mm"
include "elfzelz.mm"
include "peano2zd.mm"
include "exprecd.mm"
include "3eqtr2rd.mm"
include "peano2nn0.mm"
include "syl.mm"
include "div12d.mm"
include "3eqtr4d.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "halfcl.mm"
include "fsummulc1.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "1mhlfehlf.mm"
include "oveq12d.mm"
include "simpr.mm"
include "divrec2d.mm"
include "ax-1cn.mm"
include "nnnn0.mm"
include "nnrecred.mm"
include "recnd.mm"
include "subcl.mm"
include "0re.mm"
include "halfgt0.mm"
include "gtneii.mm"
include "mulassd.mm"
include "divcan1d.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "halfre.mm"
include "halflt1.mm"
include "ltneii.mm"
include "geoser.mm"
include "mulid2.mm"
include "eqcomd.mm"
include "subdird.mm"
include "3eqtrd.mm"

theorem geo2sum
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vj: setvar j

  disjoint A k
  disjoint N k
  disjoint j k
  disjoint A j
  disjoint N j
  assert |- ( ( N e. NN /\ A e. CC ) -> sum_ k e. ( 1 ... N ) ( A / ( 2 ^ k ) ) = ( A - ( A / ( 2 ^ N ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    #
    c1
    cN
    cfz
    co
    #
    cA
    c2
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    vk
    csu
    c1
    c1
    cmin
    co
    #
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    c2
    vj
    cv
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    vj
    csu
    #
    cc0
    @8
    cfz
    co
    #
    c1
    c2
    cdiv
    co
    #
    @10
    cexp
    co
    #
    vj
    csu
    #
    cA
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cA
    c2
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @2
    @6
    @13
    vk
    vj
    c1
    c1
    cN
    @2
    1zzd
    #
    @24
    @0
    cN
    cz
    wcel
    @1
    cN
    nnz
    adantr
    #
    @2
    @4
    @3
    wcel
    #
    wa
    #
    cA
    @5
    @0
    @1
    @26
    simplr
    @27
    @5
    @27
    c2
    cn
    wcel
    #
    @4
    cn0
    wcel
    @5
    cn
    wcel
    2nn
    @27
    @4
    @26
    @4
    cn
    wcel
    @2
    @4
    cN
    elfznn
    adantl
    nnnn0d
    c2
    @4
    nnexpcl
    sylancr
    #
    nncnd
    @27
    @5
    @29
    nnne0d
    divcld
    @4
    @11
    wceq
    @5
    @12
    cA
    cdiv
    @4
    @11
    c2
    cexp
    oveq2
    oveq2d
    fsumshftm
    @2
    @14
    @15
    @13
    vj
    csu
    #
    @20
    @9
    @15
    @13
    vj
    @7
    cc0
    @8
    cfz
    1m1e0
    oveq1i
    sumeq1i
    @2
    @30
    @15
    @17
    @19
    cmul
    co
    #
    vj
    csu
    @20
    @2
    @15
    @13
    @31
    vj
    @2
    @10
    @15
    wcel
    #
    wa
    #
    cA
    c1
    @12
    cdiv
    co
    #
    cmul
    co
    cA
    @17
    c2
    cdiv
    co
    #
    cmul
    co
    @13
    @31
    @33
    @34
    @35
    cA
    cmul
    @33
    @35
    @17
    @16
    cmul
    co
    #
    @16
    @11
    cexp
    co
    #
    @34
    @33
    @17
    c2
    @33
    @16
    cc
    wcel
    #
    @10
    cn0
    wcel
    #
    @17
    cc
    wcel
    halfcn
    @32
    @39
    @2
    @10
    @8
    elfznn0
    adantl
    #
    @16
    @10
    expcl
    sylancr
    #
    @33
    2cnd
    #
    c2
    cc0
    wne
    #
    @33
    2ne0
    a1i
    #
    divrecd
    @33
    @38
    @39
    @37
    @36
    wceq
    halfcn
    @40
    @16
    @10
    expp1
    sylancr
    @33
    c2
    @11
    @42
    @44
    @32
    @11
    cz
    wcel
    @2
    @32
    @10
    @10
    cc0
    @8
    elfzelz
    peano2zd
    adantl
    exprecd
    3eqtr2rd
    oveq2d
    @33
    cA
    @12
    @0
    @1
    @32
    simplr
    #
    @33
    @12
    @33
    @28
    @11
    cn0
    wcel
    #
    @12
    cn
    wcel
    2nn
    @33
    @39
    @46
    @40
    @10
    peano2nn0
    syl
    c2
    @11
    nnexpcl
    sylancr
    #
    nncnd
    @33
    @12
    @47
    nnne0d
    divrecd
    @33
    @17
    cA
    c2
    @41
    @45
    @42
    @44
    div12d
    3eqtr4d
    sumeq2dv
    @2
    @15
    @17
    @19
    vj
    @2
    cc0
    @8
    fzfid
    @1
    @19
    cc
    wcel
    @0
    cA
    halfcl
    adantl
    @41
    fsummulc1
    eqtr4d
    syl5eq
    @2
    c1
    @16
    cN
    cexp
    co
    #
    cmin
    co
    #
    c1
    @16
    cmin
    co
    #
    cdiv
    co
    #
    @19
    cmul
    co
    #
    c1
    c1
    @21
    cdiv
    co
    #
    cmin
    co
    #
    cA
    cmul
    co
    #
    @20
    @23
    @2
    @52
    @54
    @16
    cdiv
    co
    #
    @16
    cA
    cmul
    co
    #
    cmul
    co
    @56
    @16
    cmul
    co
    #
    cA
    cmul
    co
    @55
    @2
    @51
    @56
    @19
    @57
    cmul
    @2
    @49
    @54
    @50
    @16
    cdiv
    @2
    @48
    @53
    c1
    cmin
    @2
    c2
    cN
    @2
    2cnd
    #
    @43
    @2
    2ne0
    a1i
    #
    @25
    exprecd
    oveq2d
    @50
    @16
    wceq
    @2
    1mhlfehlf
    a1i
    oveq12d
    @2
    cA
    c2
    @0
    @1
    simpr
    #
    @59
    @60
    divrec2d
    oveq12d
    @2
    @56
    @16
    cA
    @2
    @54
    @16
    @2
    c1
    cc
    wcel
    #
    @53
    cc
    wcel
    @54
    cc
    wcel
    ax-1cn
    @2
    @53
    @2
    @21
    @2
    @28
    cN
    cn0
    wcel
    #
    @21
    cn
    wcel
    2nn
    @0
    @63
    @1
    cN
    nnnn0
    adantr
    #
    c2
    cN
    nnexpcl
    sylancr
    #
    nnrecred
    recnd
    #
    c1
    @53
    subcl
    sylancr
    #
    @38
    @2
    halfcn
    a1i
    #
    @16
    cc0
    wne
    @2
    cc0
    @16
    0re
    halfgt0
    gtneii
    a1i
    #
    divcld
    @68
    @61
    mulassd
    @2
    @58
    @54
    cA
    cmul
    @2
    @54
    @16
    @67
    @68
    @69
    divcan1d
    oveq1d
    3eqtr2d
    @2
    @18
    @51
    @19
    cmul
    @2
    @16
    vj
    cN
    @68
    @16
    c1
    wne
    @2
    @16
    c1
    halfre
    halflt1
    ltneii
    a1i
    @64
    geoser
    oveq1d
    @2
    @23
    c1
    cA
    cmul
    co
    #
    @53
    cA
    cmul
    co
    #
    cmin
    co
    @55
    @2
    cA
    @70
    @22
    @71
    cmin
    @2
    @70
    cA
    @1
    @70
    cA
    wceq
    @0
    cA
    mulid2
    adantl
    eqcomd
    @2
    cA
    @21
    @61
    @2
    @21
    @65
    nncnd
    @2
    @21
    @65
    nnne0d
    divrec2d
    oveq12d
    @2
    c1
    @53
    cA
    @62
    @2
    ax-1cn
    a1i
    @66
    @61
    subdird
    eqtr4d
    3eqtr4d
    3eqtrd
end
