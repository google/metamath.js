include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "cfa.mm"
include "clog.mm"
include "cmin.mm"
include "cmpt.mm"
include "cof.mm"
include "co1.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "cr.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "a1i.mm"
include "wa.mm"
include "ovexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "trud.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "relogcl.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "faccl.mm"
include "3syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "nnncan2d.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "cchp.mm"
include "cc.mm"
include "1red.mm"
include "chpo1ub.mm"
include "rpre.mm"
include "chpcl.mm"
include "subcld.mm"
include "cabs.mm"
include "cmul.mm"
include "adantr.mm"
include "remulcld.mm"
include "nndivre.mm"
include "syl2an.mm"
include "reflcl.mm"
include "resubcld.mm"
include "vmage0.mm"
include "fracle1.mm"
include "lemul2ad.mm"
include "subdid.mm"
include "wne.mm"
include "rpcn.mm"
include "rpcnne0.mm"
include "w3a.mm"
include "div23.mm"
include "divass.mm"
include "eqtr3d.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "mulid1d.mm"
include "3brtr3d.mm"
include "fsumle.mm"
include "fsummulc1.mm"
include "logfac2.mm"
include "oveq12d.mm"
include "fsumsub.mm"
include "chpval.mm"
include "3brtr4d.mm"
include "clt.mm"
include "wb.mm"
include "rpregt0.mm"
include "lediv1.mm"
include "mpbid.mm"
include "divsubdir.mm"
include "rpne0.mm"
include "divcan4d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "flle.mm"
include "subge0d.mm"
include "mpbird.mm"
include "mulge0d.mm"
include "breqtrd.mm"
include "fsumge0.mm"
include "breqtrrd.mm"
include "divge0.mm"
include "syl21anc.mm"
include "absidd.mm"
include "eqtrd.mm"
include "chpge0.mm"
include "ad2antrl.mm"
include "o1le.mm"
include "crli.mm"
include "logfacrlim.mm"
include "rlimo1.mm"
include "ax-mp.mm"
include "o1sub.mm"
include "mp2an.mm"
include "eqeltrri.mm"

theorem vmadivsum
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vy: setvar y

  disjoint n x
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint n y
  disjoint x y
  assert |- ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) / n ) - ( log ` x ) ) ) e. O(1)

  proof
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @3
    cdiv
    co
    #
    vn
    csu
    #
    @1
    cfa
    cfv
    #
    clog
    cfv
    #
    @0
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    #
    vx
    crp
    @0
    clog
    cfv
    #
    @9
    cmin
    co
    #
    cmpt
    #
    cmin
    cof
    co
    #
    vx
    crp
    @6
    @12
    cmin
    co
    #
    cmpt
    #
    co1
    @15
    vx
    crp
    @10
    @13
    cmin
    co
    #
    cmpt
    #
    @17
    @15
    @19
    wceq
    wtru
    vx
    crp
    @10
    @13
    cmin
    @11
    @14
    cvv
    cvv
    cvv
    crp
    cvv
    wcel
    wtru
    crp
    cr
    reex
    rpssre
    ssexi
    a1i
    wtru
    @0
    crp
    wcel
    #
    wa
    #
    @6
    @9
    cmin
    ovexd
    @21
    @12
    @9
    cmin
    ovexd
    wtru
    @11
    eqidd
    wtru
    @14
    eqidd
    offval2
    trud
    vx
    crp
    @18
    @16
    @20
    @6
    @12
    @9
    @20
    @6
    @20
    @2
    @5
    vn
    @20
    c1
    @1
    fzfid
    #
    @20
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @3
    @24
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @23
    @25
    @20
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    vmacl
    syl
    #
    @27
    nndivred
    #
    fsumrecl
    #
    recnd
    #
    @20
    @12
    @0
    relogcl
    recnd
    @20
    @9
    @8
    cr
    wcel
    @20
    @9
    cr
    wcel
    @20
    @7
    @20
    @7
    @20
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    wa
    #
    @1
    cn0
    wcel
    @7
    cn
    wcel
    @0
    rprege0
    #
    @0
    flge0nn0
    @1
    faccl
    3syl
    nnrpd
    relogcld
    #
    @8
    @0
    rerpdivcl
    mpancom
    recnd
    #
    nnncan2d
    mpteq2ia
    eqtri
    @11
    co1
    wcel
    #
    @14
    co1
    wcel
    #
    @15
    co1
    wcel
    @37
    wtru
    vx
    crp
    @0
    cchp
    cfv
    #
    @0
    cdiv
    co
    #
    @10
    c1
    cc
    wtru
    1red
    vx
    crp
    @40
    cmpt
    co1
    wcel
    wtru
    vx
    chpo1ub
    a1i
    @20
    @40
    cc
    wcel
    wtru
    @20
    @40
    @39
    cr
    wcel
    #
    @20
    @40
    cr
    wcel
    @20
    @32
    @41
    @0
    rpre
    #
    @0
    chpcl
    syl
    #
    @39
    @0
    rerpdivcl
    mpancom
    #
    recnd
    adantl
    @20
    @10
    cc
    wcel
    wtru
    @20
    @6
    @9
    @31
    @36
    subcld
    adantl
    @20
    @10
    cabs
    cfv
    #
    @40
    cabs
    cfv
    #
    cle
    wbr
    wtru
    c1
    @0
    cle
    wbr
    @20
    @6
    @0
    cmul
    co
    #
    @8
    cmin
    co
    #
    @0
    cdiv
    co
    #
    @40
    @45
    @46
    cle
    @20
    @48
    @39
    cle
    wbr
    #
    @49
    @40
    cle
    wbr
    #
    @20
    @2
    @5
    @0
    cmul
    co
    #
    @4
    @0
    @3
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    vn
    csu
    #
    @2
    @4
    vn
    csu
    #
    @48
    @39
    cle
    @20
    @2
    @56
    @4
    vn
    @22
    @24
    @52
    @55
    @24
    @5
    @0
    @29
    @20
    @32
    @23
    @42
    adantr
    remulcld
    #
    @24
    @4
    @54
    @28
    @24
    @53
    cr
    wcel
    #
    @54
    cr
    wcel
    @20
    @32
    @25
    @60
    @23
    @42
    @26
    @0
    @3
    nndivre
    syl2an
    #
    @53
    reflcl
    syl
    #
    remulcld
    #
    resubcld
    #
    @28
    @24
    @4
    @53
    @54
    cmin
    co
    #
    cmul
    co
    #
    @4
    c1
    cmul
    co
    @56
    @4
    cle
    @24
    @65
    c1
    @4
    @24
    @53
    @54
    @61
    @62
    resubcld
    #
    @24
    1red
    @28
    @24
    @25
    cc0
    @4
    cle
    wbr
    @27
    @3
    vmage0
    syl
    #
    @24
    @60
    @65
    c1
    cle
    wbr
    @61
    @53
    fracle1
    syl
    lemul2ad
    @24
    @66
    @4
    @53
    cmul
    co
    #
    @55
    cmin
    co
    @56
    @24
    @4
    @53
    @54
    @24
    @4
    @28
    recnd
    #
    @24
    @53
    @61
    recnd
    @24
    @54
    @62
    recnd
    subdid
    @24
    @52
    @69
    @55
    cmin
    @24
    @4
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    #
    @52
    @69
    wceq
    @70
    @20
    @72
    @23
    @0
    rpcn
    #
    adantr
    @24
    @3
    crp
    wcel
    @73
    @24
    @3
    @27
    nnrpd
    @3
    rpcnne0
    syl
    @71
    @72
    @73
    w3a
    @4
    @0
    cmul
    co
    @3
    cdiv
    co
    @52
    @69
    @4
    @0
    @3
    div23
    @4
    @0
    @3
    divass
    eqtr3d
    syl3anc
    oveq1d
    eqtr4d
    #
    @24
    @4
    @70
    mulid1d
    3brtr3d
    fsumle
    @20
    @48
    @2
    @52
    vn
    csu
    #
    @2
    @55
    vn
    csu
    #
    cmin
    co
    @57
    @20
    @47
    @76
    @8
    @77
    cmin
    @20
    @2
    @5
    @0
    vn
    @22
    @74
    @24
    @5
    @29
    recnd
    fsummulc1
    @20
    @33
    @8
    @77
    wceq
    @34
    @0
    vn
    logfac2
    syl
    oveq12d
    @20
    @2
    @52
    @55
    vn
    @22
    @24
    @52
    @59
    recnd
    @24
    @55
    @63
    recnd
    fsumsub
    eqtr4d
    #
    @20
    @32
    @39
    @58
    wceq
    @42
    @0
    vn
    chpval
    syl
    3brtr4d
    @20
    @48
    cr
    wcel
    #
    @41
    @32
    cc0
    @0
    clt
    wbr
    wa
    #
    @50
    @51
    wb
    @20
    @47
    @8
    @20
    @6
    @0
    @30
    @42
    remulcld
    #
    @35
    resubcld
    #
    @43
    @0
    rpregt0
    #
    @48
    @39
    @0
    lediv1
    syl3anc
    mpbid
    @20
    @45
    @49
    cabs
    cfv
    @49
    @20
    @10
    @49
    cabs
    @20
    @49
    @47
    @0
    cdiv
    co
    #
    @9
    cmin
    co
    #
    @10
    @20
    @47
    cc
    wcel
    @8
    cc
    wcel
    @72
    @0
    cc0
    wne
    wa
    @49
    @85
    wceq
    @20
    @47
    @81
    recnd
    @20
    @8
    @35
    recnd
    @0
    rpcnne0
    @47
    @8
    @0
    divsubdir
    syl3anc
    @20
    @84
    @6
    @9
    cmin
    @20
    @6
    @0
    @31
    @74
    @0
    rpne0
    divcan4d
    oveq1d
    eqtr2d
    fveq2d
    @20
    @49
    @79
    @20
    @49
    cr
    wcel
    @82
    @48
    @0
    rerpdivcl
    mpancom
    @20
    @79
    cc0
    @48
    cle
    wbr
    @80
    cc0
    @49
    cle
    wbr
    @82
    @20
    cc0
    @57
    @48
    cle
    @20
    @2
    @56
    vn
    @22
    @64
    @24
    cc0
    @66
    @56
    cle
    @24
    @4
    @65
    @28
    @67
    @68
    @24
    cc0
    @65
    cle
    wbr
    @54
    @53
    cle
    wbr
    #
    @24
    @60
    @86
    @61
    @53
    flle
    syl
    @24
    @53
    @54
    @61
    @62
    subge0d
    mpbird
    mulge0d
    @75
    breqtrd
    fsumge0
    @78
    breqtrrd
    @83
    @48
    @0
    divge0
    syl21anc
    absidd
    eqtrd
    @20
    @40
    @44
    @20
    @41
    cc0
    @39
    cle
    wbr
    #
    @80
    cc0
    @40
    cle
    wbr
    @43
    @20
    @32
    @87
    @42
    @0
    chpge0
    syl
    @83
    @39
    @0
    divge0
    syl21anc
    absidd
    3brtr4d
    ad2antrl
    o1le
    trud
    @14
    c1
    crli
    wbr
    @38
    vx
    logfacrlim
    c1
    @14
    rlimo1
    ax-mp
    @11
    @14
    o1sub
    mp2an
    eqeltrri
end
