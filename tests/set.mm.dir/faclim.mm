include "cn0.mm"
include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cn.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "cmpt.mm"
include "cfa.mm"
include "cfv.mm"
include "cli.mm"
include "wceq.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "wbr.mm"
include "cc0.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "fveq2.mm"
include "fac0.mm"
include "syl6eq.mm"
include "breq12d.mm"
include "weq.mm"
include "csn.mm"
include "cxp.mm"
include "1red.mm"
include "nnrecre.mm"
include "readdcld.mm"
include "recnd.mm"
include "exp0d.mm"
include "nncn.mm"
include "nnne0.mm"
include "div0d.mm"
include "1p0e1.mm"
include "1div1e1.mm"
include "mpteq2ia.mm"
include "fconstmpt.mm"
include "eqtr4i.mm"
include "wtru.mm"
include "nnuz.mm"
include "1zzd.mm"
include "climprod1.mm"
include "trud.mm"
include "eqbrtri.mm"
include "wa.mm"
include "cvv.mm"
include "simpr.mm"
include "seqex.mm"
include "a1i.mm"
include "faclimlem2.mm"
include "adantr.mm"
include "cc.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "adantl.mm"
include "cfz.mm"
include "wf.mm"
include "crp.mm"
include "1rp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpaddcld.mm"
include "cz.mm"
include "nn0z.mm"
include "rpexpcld.mm"
include "1cnd.mm"
include "nn0nndivcl.mm"
include "addcomd.mm"
include "nn0ge0div.mm"
include "ge0p1rpd.mm"
include "eqeltrd.mm"
include "rpdivcld.mm"
include "rpcnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "adantlr.mm"
include "mulcl.mm"
include "seqcl.mm"
include "rpmulcld.mm"
include "nn0p1nn.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "faclimlem3.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "3eqtr4d.mm"
include "sylan2.mm"
include "prodfmul.mm"
include "climmul.mm"
include "facp1.mm"
include "breqtrrd.mm"
include "ex.mm"
include "nn0ind.mm"
include "syl5eqbr.mm"

theorem faclim
  let cA: class A
  let vn: setvar n
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  assume faclim.1: |- F = ( n e. NN |-> ( ( ( 1 + ( 1 / n ) ) ^ A ) / ( 1 + ( A / n ) ) ) )

  disjoint A n
  disjoint A a
  disjoint A b
  disjoint A m
  disjoint A x
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint m n
  disjoint m x
  disjoint n x
  assert |- ( A e. NN0 -> seq 1 ( x. , F ) ~~> ( ! ` A ) )

  proof
    cA
    cn0
    wcel
    cmul
    cF
    c1
    cseq
    #
    cmul
    vn
    cn
    c1
    c1
    vn
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cexp
    co
    #
    c1
    cA
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    #
    cA
    cfa
    cfv
    #
    cli
    cF
    @8
    wceq
    @0
    @9
    wceq
    faclim.1
    cmul
    cF
    @8
    c1
    seqeq3
    ax-mp
    cmul
    vn
    cn
    @3
    va
    cv
    #
    cexp
    co
    #
    c1
    @11
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    #
    @11
    cfa
    cfv
    #
    cli
    wbr
    cmul
    vn
    cn
    @3
    cc0
    cexp
    co
    #
    c1
    cc0
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    #
    c1
    cli
    wbr
    cmul
    vn
    cn
    @3
    vm
    cv
    #
    cexp
    co
    #
    c1
    @25
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    #
    @25
    cfa
    cfv
    #
    cli
    wbr
    #
    cmul
    vn
    cn
    @3
    @25
    c1
    caddc
    co
    #
    cexp
    co
    #
    c1
    @34
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    #
    @34
    cfa
    cfv
    #
    cli
    wbr
    #
    @9
    @10
    cli
    wbr
    va
    vm
    cA
    @11
    cc0
    wceq
    #
    @17
    @24
    @18
    c1
    cli
    @43
    @16
    @23
    cmul
    c1
    @43
    vn
    cn
    @15
    @22
    @43
    @12
    @19
    @14
    @21
    cdiv
    @11
    cc0
    @3
    cexp
    oveq2
    @43
    @13
    @20
    c1
    caddc
    @11
    cc0
    @1
    cdiv
    oveq1
    oveq2d
    oveq12d
    mpteq2dv
    seqeq3d
    @43
    @18
    cc0
    cfa
    cfv
    c1
    @11
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    breq12d
    va
    vm
    weq
    #
    @17
    @31
    @18
    @32
    cli
    @44
    @16
    @30
    cmul
    c1
    @44
    vn
    cn
    @15
    @29
    @44
    @12
    @26
    @14
    @28
    cdiv
    @11
    @25
    @3
    cexp
    oveq2
    @44
    @13
    @27
    c1
    caddc
    @11
    @25
    @1
    cdiv
    oveq1
    oveq2d
    oveq12d
    mpteq2dv
    seqeq3d
    @11
    @25
    cfa
    fveq2
    breq12d
    @11
    @34
    wceq
    #
    @17
    @40
    @18
    @41
    cli
    @45
    @16
    @39
    cmul
    c1
    @45
    vn
    cn
    @15
    @38
    @45
    @12
    @35
    @14
    @37
    cdiv
    @11
    @34
    @3
    cexp
    oveq2
    @45
    @13
    @36
    c1
    caddc
    @11
    @34
    @1
    cdiv
    oveq1
    oveq2d
    oveq12d
    mpteq2dv
    seqeq3d
    @11
    @34
    cfa
    fveq2
    breq12d
    @11
    cA
    wceq
    #
    @17
    @9
    @18
    @10
    cli
    @46
    @16
    @8
    cmul
    c1
    @46
    vn
    cn
    @15
    @7
    @46
    @12
    @4
    @14
    @6
    cdiv
    @11
    cA
    @3
    cexp
    oveq2
    @46
    @13
    @5
    c1
    caddc
    @11
    cA
    @1
    cdiv
    oveq1
    oveq2d
    oveq12d
    mpteq2dv
    seqeq3d
    @11
    cA
    cfa
    fveq2
    breq12d
    @24
    cmul
    cn
    c1
    csn
    cxp
    #
    c1
    cseq
    #
    c1
    cli
    @23
    @47
    wceq
    @24
    @48
    wceq
    @23
    vn
    cn
    c1
    cmpt
    @47
    vn
    cn
    @22
    c1
    @1
    cn
    wcel
    #
    @22
    c1
    c1
    cdiv
    co
    c1
    @49
    @19
    c1
    @21
    c1
    cdiv
    @49
    @3
    @49
    @3
    @49
    c1
    @2
    @49
    1red
    @1
    nnrecre
    readdcld
    recnd
    exp0d
    @49
    @21
    c1
    cc0
    caddc
    co
    c1
    @49
    @20
    cc0
    c1
    caddc
    @49
    @1
    @1
    nncn
    @1
    nnne0
    div0d
    oveq2d
    1p0e1
    syl6eq
    oveq12d
    1div1e1
    syl6eq
    mpteq2ia
    vn
    cn
    c1
    fconstmpt
    eqtr4i
    cmul
    @23
    @47
    c1
    seqeq3
    ax-mp
    @48
    c1
    cli
    wbr
    wtru
    c1
    cn
    nnuz
    wtru
    1zzd
    climprod1
    trud
    eqbrtri
    @25
    cn0
    wcel
    #
    @33
    @42
    @50
    @33
    wa
    #
    @40
    @32
    @34
    cmul
    co
    #
    @41
    cli
    @51
    @32
    @34
    va
    @31
    cmul
    vn
    cn
    @28
    @3
    cmul
    co
    #
    @37
    cdiv
    co
    #
    cmpt
    #
    c1
    cseq
    #
    @40
    c1
    cvv
    cn
    nnuz
    @51
    1zzd
    @50
    @33
    simpr
    @40
    cvv
    wcel
    @51
    cmul
    @39
    c1
    seqex
    a1i
    @50
    @56
    @34
    cli
    wbr
    @33
    vn
    @25
    faclimlem2
    adantr
    @50
    @11
    cn
    wcel
    #
    @11
    @31
    cfv
    #
    cc
    wcel
    @33
    @50
    @57
    wa
    #
    vb
    vx
    cmul
    cc
    @30
    c1
    @11
    @57
    @11
    c1
    cuz
    cfv
    wcel
    #
    @50
    @57
    @60
    @11
    elnnuz
    biimpi
    adantl
    #
    @50
    vb
    cv
    #
    c1
    @11
    cfz
    co
    wcel
    #
    @62
    @30
    cfv
    #
    cc
    wcel
    #
    @57
    @50
    cn
    cc
    @30
    wf
    @62
    cn
    wcel
    #
    @65
    @63
    @50
    vn
    cn
    @29
    cc
    @30
    @50
    @49
    wa
    #
    @29
    @67
    @26
    @28
    @67
    @3
    @25
    @67
    c1
    @2
    c1
    crp
    wcel
    @67
    1rp
    a1i
    #
    @49
    @2
    crp
    wcel
    @50
    @49
    @1
    @1
    nnrp
    #
    rpreccld
    adantl
    rpaddcld
    #
    @50
    @25
    cz
    wcel
    @49
    @25
    nn0z
    adantr
    rpexpcld
    @67
    @28
    @27
    c1
    caddc
    co
    crp
    @67
    c1
    @27
    @67
    1cnd
    @67
    @27
    @25
    @1
    nn0nndivcl
    #
    recnd
    addcomd
    @67
    @27
    @71
    @25
    @1
    nn0ge0div
    ge0p1rpd
    eqeltrd
    #
    rpdivcld
    rpcnd
    @30
    eqid
    #
    fmptd
    @62
    @11
    elfznn
    #
    cn
    cc
    @62
    @30
    ffvelrn
    syl2an
    adantlr
    #
    @62
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    @62
    @76
    cmul
    co
    cc
    wcel
    @59
    @62
    @76
    mulcl
    adantl
    #
    seqcl
    adantlr
    @50
    @57
    @11
    @56
    cfv
    #
    cc
    wcel
    @33
    @59
    vb
    vx
    cmul
    cc
    @55
    c1
    @11
    @61
    @50
    @63
    @62
    @55
    cfv
    #
    cc
    wcel
    #
    @57
    @50
    cn
    cc
    @55
    wf
    @66
    @80
    @63
    @50
    vn
    cn
    @54
    cc
    @55
    @67
    @54
    @67
    @53
    @37
    @67
    @28
    @3
    @72
    @70
    rpmulcld
    @67
    c1
    @36
    @68
    @50
    @34
    crp
    wcel
    @1
    crp
    wcel
    @36
    crp
    wcel
    @49
    @50
    @34
    @25
    nn0p1nn
    nnrpd
    @69
    @34
    @1
    rpdivcl
    syl2an
    rpaddcld
    rpdivcld
    rpcnd
    @55
    eqid
    #
    fmptd
    @74
    cn
    cc
    @62
    @55
    ffvelrn
    syl2an
    adantlr
    #
    @77
    seqcl
    adantlr
    @50
    @57
    @11
    @40
    cfv
    @58
    @78
    cmul
    co
    wceq
    @33
    @59
    vb
    @30
    @55
    @39
    c1
    @11
    @61
    @75
    @82
    @50
    @63
    @62
    @39
    cfv
    #
    @64
    @79
    cmul
    co
    #
    wceq
    #
    @57
    @63
    @50
    @66
    @85
    @74
    @50
    @66
    wa
    c1
    c1
    @62
    cdiv
    co
    #
    caddc
    co
    #
    @34
    cexp
    co
    #
    c1
    @34
    @62
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    @87
    @25
    cexp
    co
    #
    c1
    @25
    @62
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    @94
    @87
    cmul
    co
    #
    @90
    cdiv
    co
    #
    cmul
    co
    #
    @83
    @84
    @62
    @25
    faclimlem3
    @66
    @83
    @91
    wceq
    @50
    vn
    @62
    @38
    @91
    cn
    @39
    vn
    vb
    weq
    #
    @35
    @88
    @37
    @90
    cdiv
    @99
    @3
    @87
    @34
    cexp
    @99
    @2
    @86
    c1
    caddc
    @1
    @62
    c1
    cdiv
    oveq2
    oveq2d
    #
    oveq1d
    @99
    @36
    @89
    c1
    caddc
    @1
    @62
    @34
    cdiv
    oveq2
    oveq2d
    #
    oveq12d
    @39
    eqid
    @88
    @90
    cdiv
    ovex
    fvmpt
    adantl
    @66
    @84
    @98
    wceq
    @50
    @66
    @64
    @95
    @79
    @97
    cmul
    vn
    @62
    @29
    @95
    cn
    @30
    @99
    @26
    @92
    @28
    @94
    cdiv
    @99
    @3
    @87
    @25
    cexp
    @100
    oveq1d
    @99
    @27
    @93
    c1
    caddc
    @1
    @62
    @25
    cdiv
    oveq2
    oveq2d
    #
    oveq12d
    @73
    @92
    @94
    cdiv
    ovex
    fvmpt
    vn
    @62
    @54
    @97
    cn
    @55
    @99
    @53
    @96
    @37
    @90
    cdiv
    @99
    @28
    @94
    @3
    @87
    cmul
    @102
    @100
    oveq12d
    @101
    oveq12d
    @81
    @96
    @90
    cdiv
    ovex
    fvmpt
    oveq12d
    adantl
    3eqtr4d
    sylan2
    adantlr
    prodfmul
    adantlr
    climmul
    @50
    @41
    @52
    wceq
    @33
    @25
    facp1
    adantr
    breqtrrd
    ex
    nn0ind
    syl5eqbr
end
