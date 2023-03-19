include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cn.mm"
include "cv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc.mm"
include "wcel.mm"
include "1cnd.mm"
include "divcnv.mm"
include "syl.mm"
include "nnex.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "peano2nn.mm"
include "adantl.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "climshft2.mm"
include "mpbird.mm"
include "seqex.mm"
include "nnrecred.mm"
include "recnd.mm"
include "eqeltrd.mm"
include "cfz.mm"
include "cmul.mm"
include "csu.mm"
include "elfznn.mm"
include "nncnd.mm"
include "peano2cn.mm"
include "nnmulcld.mm"
include "nnne0d.mm"
include "divsubdird.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "mulid1d.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "divcan5d.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "sumeq2dv.mm"
include "1div1e1.mm"
include "syl6eq.mm"
include "cz.mm"
include "nnz.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "telfsum.mm"
include "eqtrd.mm"
include "id.mm"
include "simpr.mm"
include "fsumser.mm"
include "3eqtr2rd.mm"
include "climsubc2.mm"
include "trud.mm"
include "1m0e1.mm"
include "breqtri.mm"

theorem trireciplem
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  assume trireciplem.1: |- F = ( n e. NN |-> ( 1 / ( n x. ( n + 1 ) ) ) )


  assert |- seq 1 ( + , F ) ~~> 1

  proof
    caddc
    cF
    c1
    cseq
    #
    c1
    cc0
    cmin
    co
    #
    c1
    cli
    @0
    @1
    cli
    wbr
    wtru
    cc0
    c1
    vk
    vn
    cn
    c1
    vn
    cv
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @0
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    #
    wtru
    @5
    cc0
    cli
    wbr
    vn
    cn
    c1
    @2
    cdiv
    co
    #
    cmpt
    #
    cc0
    cli
    wbr
    #
    wtru
    c1
    cc
    wcel
    #
    @9
    wtru
    1cnd
    #
    c1
    vn
    divcnv
    syl
    wtru
    cc0
    vk
    @5
    @8
    c1
    c1
    cvv
    cvv
    cn
    nnuz
    @6
    @6
    @5
    cvv
    wcel
    wtru
    vn
    cn
    @4
    nnex
    mptex
    a1i
    @8
    cvv
    wcel
    wtru
    vn
    cn
    @7
    nnex
    mptex
    a1i
    wtru
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @12
    c1
    caddc
    co
    #
    @8
    cfv
    #
    c1
    @15
    cdiv
    co
    #
    @12
    @5
    cfv
    #
    @14
    @15
    cn
    wcel
    #
    @16
    @17
    wceq
    @13
    @19
    wtru
    @12
    peano2nn
    adantl
    #
    vn
    @15
    @7
    @17
    cn
    @8
    @2
    @15
    c1
    cdiv
    oveq2
    #
    @8
    eqid
    c1
    @15
    cdiv
    ovex
    #
    fvmpt
    syl
    @13
    @18
    @17
    wceq
    wtru
    vn
    @12
    @4
    @17
    cn
    @5
    @2
    @12
    wceq
    @3
    @15
    c1
    cdiv
    @2
    @12
    c1
    caddc
    oveq1
    oveq2d
    @5
    eqid
    @22
    fvmpt
    adantl
    #
    eqtr4d
    climshft2
    mpbird
    @11
    @0
    cvv
    wcel
    wtru
    caddc
    cF
    c1
    seqex
    a1i
    @14
    @18
    @17
    cc
    @23
    @14
    @17
    @14
    @15
    @20
    nnrecred
    recnd
    eqeltrd
    @14
    c1
    @18
    cmin
    co
    c1
    @17
    cmin
    co
    #
    c1
    @12
    cfz
    co
    #
    c1
    vj
    cv
    #
    @26
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    vj
    csu
    #
    @12
    @0
    cfv
    @14
    @18
    @17
    c1
    cmin
    @23
    oveq2d
    @14
    @30
    @25
    c1
    @26
    cdiv
    co
    #
    c1
    @27
    cdiv
    co
    #
    cmin
    co
    #
    vj
    csu
    @24
    @14
    @25
    @29
    @33
    vj
    @14
    @26
    @25
    wcel
    #
    wa
    #
    @27
    @26
    cmin
    co
    #
    @28
    cdiv
    co
    @27
    @28
    cdiv
    co
    #
    @26
    @28
    cdiv
    co
    #
    cmin
    co
    @29
    @33
    @35
    @27
    @26
    @28
    @35
    @26
    cc
    wcel
    #
    @27
    cc
    wcel
    @35
    @26
    @34
    @26
    cn
    wcel
    #
    @14
    @26
    @12
    elfznn
    adantl
    #
    nncnd
    #
    @26
    peano2cn
    syl
    #
    @42
    @35
    @28
    @35
    @26
    @27
    @41
    @35
    @40
    @27
    cn
    wcel
    @41
    @26
    peano2nn
    syl
    #
    nnmulcld
    #
    nncnd
    @35
    @28
    @45
    nnne0d
    divsubdird
    @35
    @36
    c1
    @28
    cdiv
    @35
    @39
    @10
    @36
    c1
    wceq
    @42
    ax-1cn
    @26
    c1
    pncan2
    sylancl
    oveq1d
    @35
    @37
    @31
    @38
    @32
    cmin
    @35
    @27
    c1
    cmul
    co
    #
    @27
    @26
    cmul
    co
    #
    cdiv
    co
    @37
    @31
    @35
    @46
    @27
    @47
    @28
    cdiv
    @35
    @27
    @43
    mulid1d
    @35
    @27
    @26
    @43
    @42
    mulcomd
    oveq12d
    @35
    c1
    @26
    @27
    @35
    1cnd
    #
    @42
    @43
    @35
    @26
    @41
    nnne0d
    #
    @35
    @27
    @44
    nnne0d
    #
    divcan5d
    eqtr3d
    @35
    @26
    c1
    cmul
    co
    #
    @28
    cdiv
    co
    @38
    @32
    @35
    @51
    @26
    @28
    cdiv
    @35
    @26
    @42
    mulid1d
    oveq1d
    @35
    c1
    @27
    @26
    @48
    @43
    @42
    @50
    @49
    divcan5d
    eqtr3d
    oveq12d
    3eqtr3d
    sumeq2dv
    @14
    @7
    @31
    @32
    c1
    vj
    vn
    @17
    c1
    @12
    @2
    @26
    c1
    cdiv
    oveq2
    @2
    @27
    c1
    cdiv
    oveq2
    @2
    c1
    wceq
    @7
    c1
    c1
    cdiv
    co
    c1
    @2
    c1
    c1
    cdiv
    oveq2
    1div1e1
    syl6eq
    @21
    @13
    @12
    cz
    wcel
    wtru
    @12
    nnz
    adantl
    @14
    @15
    cn
    c1
    cuz
    cfv
    #
    @20
    nnuz
    syl6eleq
    @14
    @2
    c1
    @15
    cfz
    co
    wcel
    #
    wa
    #
    @7
    @54
    @2
    @53
    @2
    cn
    wcel
    @14
    @2
    @15
    elfznn
    adantl
    nnrecred
    recnd
    telfsum
    eqtrd
    @14
    @29
    vj
    cF
    c1
    @12
    @35
    @40
    @26
    cF
    cfv
    @29
    wceq
    @41
    vn
    @26
    c1
    @2
    @3
    cmul
    co
    #
    cdiv
    co
    @29
    cn
    cF
    @2
    @26
    wceq
    #
    @55
    @28
    c1
    cdiv
    @56
    @2
    @26
    @3
    @27
    cmul
    @56
    id
    @2
    @26
    c1
    caddc
    oveq1
    oveq12d
    oveq2d
    trireciplem.1
    c1
    @28
    cdiv
    ovex
    fvmpt
    syl
    @14
    @12
    cn
    @52
    wtru
    @13
    simpr
    nnuz
    syl6eleq
    @35
    @29
    @35
    @28
    @45
    nnrecred
    recnd
    fsumser
    3eqtr2rd
    climsubc2
    trud
    1m0e1
    breqtri
end
