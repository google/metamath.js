include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "cmin.mm"
include "cem.mm"
include "cabs.mm"
include "caddc.mm"
include "cle.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "relogcl.mm"
include "cr.mm"
include "emre.mm"
include "a1i.mm"
include "subsub4d.mm"
include "fveq2d.mm"
include "wbr.mm"
include "rpreccl.mm"
include "rpred.mm"
include "resubcl.mm"
include "sylancr.mm"
include "cn0.mm"
include "cc0.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "syl.mm"
include "nn0p1nn.mm"
include "nnrpd.mm"
include "resubcld.mm"
include "cicc.mm"
include "harmonicbnd.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "rpre.mm"
include "fllep1.mm"
include "clt.mm"
include "wb.mm"
include "rpregt0.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lerec.mm"
include "syl12anc.mm"
include "mpbid.mm"
include "le2subd.mm"
include "sub32d.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "oveq2.mm"
include "fsumm1.mm"
include "cc.mm"
include "wceq.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "pncand.mm"
include "breqtrd.mm"
include "logleb.mm"
include "mpdan.mm"
include "lesub2dd.mm"
include "letrd.mm"
include "readdcld.mm"
include "id.mm"
include "relogdivd.mm"
include "ce.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "reefcld.mm"
include "wne.mm"
include "rpcnne0.mm"
include "divdir.mm"
include "syl3anc.mm"
include "reflcl.mm"
include "cmul.mm"
include "flle.mm"
include "rpcn.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "ledivmul.mm"
include "mpbird.mm"
include "leadd1dd.mm"
include "eqbrtrd.mm"
include "efgt1p.mm"
include "ltled.mm"
include "rpdivcl.mm"
include "rpefcld.mm"
include "logled.mm"
include "relogefd.mm"
include "eqbrtrrd.mm"
include "lesubadd2d.mm"
include "harmonicbnd3.mm"
include "0re.mm"
include "simp3bi.mm"
include "lesubaddd.mm"
include "absdifled.mm"
include "mpbir2and.mm"

theorem harmonicbnd4
  let cA: class A
  let vm: setvar m
  let cN: class N

  disjoint A m
  disjoint N m
  assert |- ( A e. RR+ -> ( abs ` ( sum_ m e. ( 1 ... ( |_ ` A ) ) ( 1 / m ) - ( ( log ` A ) + gamma ) ) ) <_ ( 1 / A ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    cA
    clog
    cfv
    #
    cmin
    co
    #
    cem
    cmin
    co
    #
    cabs
    cfv
    #
    @5
    @6
    cem
    caddc
    co
    cmin
    co
    #
    cabs
    cfv
    c1
    cA
    cdiv
    co
    #
    cle
    @0
    @8
    @10
    cabs
    @0
    @5
    @6
    cem
    @0
    @5
    @0
    @2
    @4
    vm
    @0
    c1
    @1
    fzfid
    @0
    @3
    @2
    wcel
    #
    wa
    @3
    @12
    @3
    cn
    wcel
    #
    @0
    @3
    @1
    elfznn
    adantl
    nnrecred
    fsumrecl
    #
    recnd
    #
    @0
    @6
    cA
    relogcl
    #
    recnd
    #
    @0
    cem
    cem
    cr
    wcel
    #
    @0
    emre
    a1i
    #
    recnd
    subsub4d
    fveq2d
    @0
    @9
    @11
    cle
    wbr
    cem
    @11
    cmin
    co
    #
    @7
    cle
    wbr
    @7
    cem
    @11
    caddc
    co
    cle
    wbr
    #
    @0
    @20
    @5
    @1
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    @7
    @0
    @18
    @11
    cr
    wcel
    @20
    cr
    wcel
    emre
    @0
    @11
    cA
    rpreccl
    #
    rpred
    #
    cem
    @11
    resubcl
    sylancr
    @0
    @5
    @23
    @14
    @0
    @22
    crp
    wcel
    #
    @23
    cr
    wcel
    @0
    @22
    @0
    @1
    cn0
    wcel
    #
    @22
    cn
    wcel
    #
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    wa
    @28
    cA
    rprege0
    cA
    flge0nn0
    syl
    #
    @1
    nn0p1nn
    syl
    #
    nnrpd
    #
    @22
    relogcl
    syl
    #
    resubcld
    #
    @0
    @5
    @6
    @14
    @16
    resubcld
    #
    @0
    @20
    c1
    @22
    cfz
    co
    #
    @4
    vm
    csu
    #
    @23
    cmin
    co
    #
    c1
    @22
    cdiv
    co
    #
    cmin
    co
    #
    @24
    cle
    @0
    cem
    @40
    @39
    @11
    @19
    @0
    @22
    @32
    nnrecred
    #
    @0
    @38
    @23
    @0
    @37
    @4
    vm
    @0
    c1
    @22
    fzfid
    @0
    @3
    @37
    wcel
    #
    wa
    #
    @3
    @43
    @13
    @0
    @3
    @22
    elfznn
    adantl
    nnrecred
    #
    fsumrecl
    #
    @34
    resubcld
    @26
    @0
    @39
    cem
    c1
    cicc
    co
    wcel
    #
    cem
    @39
    cle
    wbr
    #
    @0
    @29
    @47
    @32
    vm
    @22
    harmonicbnd
    syl
    @47
    @39
    cr
    wcel
    @48
    @39
    c1
    cle
    wbr
    cem
    c1
    @39
    emre
    1re
    elicc2i
    simp2bi
    syl
    @0
    cA
    @22
    cle
    wbr
    #
    @40
    @11
    cle
    wbr
    #
    @0
    @30
    @49
    cA
    rpre
    #
    cA
    fllep1
    syl
    #
    @0
    @30
    cc0
    cA
    clt
    wbr
    wa
    #
    @22
    cr
    wcel
    #
    cc0
    @22
    clt
    wbr
    @49
    @50
    wb
    cA
    rpregt0
    #
    @0
    @22
    @32
    nnred
    #
    @0
    @22
    @32
    nngt0d
    cA
    @22
    lerec
    syl12anc
    mpbid
    le2subd
    @0
    @41
    @38
    @40
    cmin
    co
    #
    @23
    cmin
    co
    @24
    @0
    @38
    @23
    @40
    @0
    @38
    @46
    recnd
    @0
    @23
    @34
    recnd
    @0
    @40
    @42
    recnd
    #
    sub32d
    @0
    @57
    @5
    @23
    cmin
    @0
    @57
    @5
    @40
    caddc
    co
    #
    @40
    cmin
    co
    @5
    @0
    @38
    @59
    @40
    cmin
    @0
    @38
    c1
    @22
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    vm
    csu
    #
    @40
    caddc
    co
    @59
    @0
    @4
    @40
    vm
    c1
    @22
    @0
    @22
    cn
    c1
    cuz
    cfv
    @32
    nnuz
    syl6eleq
    @44
    @4
    @45
    recnd
    @3
    @22
    c1
    cdiv
    oveq2
    fsumm1
    @0
    @62
    @5
    @40
    caddc
    @0
    @61
    @2
    @4
    vm
    @0
    @60
    @1
    c1
    cfz
    @0
    @1
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @60
    @1
    wceq
    @0
    @1
    @31
    nn0cnd
    #
    ax-1cn
    @1
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
    oveq1d
    @0
    @5
    @40
    @15
    @58
    pncand
    eqtrd
    oveq1d
    eqtrd
    breqtrd
    @0
    @6
    @23
    @5
    @16
    @34
    @14
    @0
    @49
    @6
    @23
    cle
    wbr
    #
    @52
    @0
    @27
    @49
    @66
    wb
    @33
    cA
    @22
    logleb
    mpdan
    mpbid
    lesub2dd
    letrd
    @0
    @7
    @11
    cmin
    co
    #
    cem
    cle
    wbr
    @21
    @0
    @67
    @24
    cem
    @0
    @7
    @11
    @36
    @26
    resubcld
    @35
    @19
    @0
    @67
    @5
    @6
    @11
    caddc
    co
    #
    cmin
    co
    @24
    cle
    @0
    @5
    @6
    @11
    @15
    @17
    @0
    @11
    @26
    recnd
    subsub4d
    @0
    @23
    @68
    @5
    @34
    @0
    @6
    @11
    @16
    @26
    readdcld
    @14
    @0
    @23
    @6
    cmin
    co
    #
    @11
    cle
    wbr
    @23
    @68
    cle
    wbr
    @0
    @22
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    @69
    @11
    cle
    @0
    @22
    cA
    @33
    @0
    id
    relogdivd
    @0
    @71
    @11
    ce
    cfv
    #
    clog
    cfv
    #
    @11
    cle
    @0
    @70
    @72
    cle
    wbr
    @71
    @73
    cle
    wbr
    @0
    @70
    c1
    @11
    caddc
    co
    #
    @72
    @54
    @0
    @70
    cr
    wcel
    @56
    @22
    cA
    rerpdivcl
    mpancom
    @0
    c1
    @11
    c1
    cr
    wcel
    #
    @0
    1re
    a1i
    #
    @26
    readdcld
    #
    @0
    @11
    @26
    reefcld
    #
    @0
    @70
    @1
    cA
    cdiv
    co
    #
    @11
    caddc
    co
    #
    @74
    cle
    @0
    @63
    @64
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    @70
    @80
    wceq
    @65
    @64
    @0
    ax-1cn
    a1i
    cA
    rpcnne0
    @1
    c1
    cA
    divdir
    syl3anc
    @0
    @79
    c1
    @11
    @1
    cr
    wcel
    #
    @0
    @79
    cr
    wcel
    @0
    @30
    @81
    @51
    cA
    reflcl
    syl
    #
    @1
    cA
    rerpdivcl
    mpancom
    @76
    @26
    @0
    @79
    c1
    cle
    wbr
    #
    @1
    cA
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @1
    cA
    @84
    cle
    @0
    @30
    @1
    cA
    cle
    wbr
    @51
    cA
    flle
    syl
    @0
    cA
    cA
    rpcn
    mulid1d
    breqtrrd
    @0
    @81
    @75
    @53
    @83
    @85
    wb
    @82
    @76
    @55
    @1
    c1
    cA
    ledivmul
    syl3anc
    mpbird
    leadd1dd
    eqbrtrd
    @0
    @74
    @72
    @77
    @78
    @0
    @11
    crp
    wcel
    @74
    @72
    clt
    wbr
    @25
    @11
    efgt1p
    syl
    ltled
    letrd
    @0
    @70
    @72
    @27
    @0
    @70
    crp
    wcel
    @33
    @22
    cA
    rpdivcl
    mpancom
    @0
    @11
    @26
    rpefcld
    logled
    mpbid
    @0
    @11
    @26
    relogefd
    breqtrd
    eqbrtrrd
    @0
    @23
    @6
    @11
    @34
    @16
    @26
    lesubadd2d
    mpbid
    lesub2dd
    eqbrtrd
    @0
    @24
    cc0
    cem
    cicc
    co
    wcel
    #
    @24
    cem
    cle
    wbr
    #
    @0
    @28
    @86
    @31
    vm
    @1
    harmonicbnd3
    syl
    @86
    @24
    cr
    wcel
    cc0
    @24
    cle
    wbr
    @87
    cc0
    cem
    @24
    0re
    emre
    elicc2i
    simp3bi
    syl
    letrd
    @0
    @7
    @11
    cem
    @36
    @26
    @19
    lesubaddd
    mpbid
    @0
    @7
    cem
    @11
    @36
    @19
    @26
    absdifled
    mpbir2and
    eqbrtrrd
end
