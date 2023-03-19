include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc0.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "cc.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "divcnv.mm"
include "ax-mp.mm"
include "eqbrtri.mm"
include "a1i.mm"
include "caddc.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "cfv.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "id.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "fvmptd.mm"
include "nnrecre.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "oveq1d.mm"
include "2re.mm"
include "nnre.mm"
include "remulcld.mm"
include "cle.mm"
include "0le2.mm"
include "rpge0d.mm"
include "mulge0d.mm"
include "ge0p1rpd.mm"
include "rpred.mm"
include "1red.mm"
include "0le1.mm"
include "readdcld.mm"
include "clt.mm"
include "nncn.mm"
include "mulid2d.mm"
include "1lt2.mm"
include "ltmul1dd.mm"
include "eqbrtrrd.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "ltled.mm"
include "lediv2ad.mm"
include "3brtr4d.mm"
include "breqtrrd.mm"
include "climsqz2.mm"
include "1cnd.mm"
include "recnd.mm"
include "2cnd.mm"
include "mulcld.mm"
include "addcld.mm"
include "rpne0d.mm"
include "reccld.mm"
include "subcld.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "climsubc2.mm"
include "1m0e1.mm"
include "syl6breq.mm"
include "halfcld.mm"
include "cexp.mm"
include "sqcld.mm"
include "adddid.mm"
include "mul12d.mm"
include "sqvald.mm"
include "mulid1d.mm"
include "oveq12d.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "cz.mm"
include "2z.mm"
include "rpexpcld.mm"
include "rphalfcld.mm"
include "rpaddcld.mm"
include "divmuldivd.mm"
include "pncand.mm"
include "divsubdird.mm"
include "dividd.mm"
include "nnne0.mm"
include "divcld.mm"
include "divne0d.mm"
include "divcan5rd.mm"
include "divcan6d.mm"
include "adddird.mm"
include "div12d.mm"
include "1e2m1.mm"
include "oveq2i.mm"
include "exp1d.mm"
include "expm1d.mm"
include "3eqtr3a.mm"
include "eqtr3d.mm"
include "3eqtr2d.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "climmulc2.mm"
include "trud.mm"
include "halfcn.mm"
include "mulid1i.mm"
include "breqtri.mm"

theorem stirlinglem1
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cL: class L
  let vk: setvar k
  let vx: setvar x
  assume stirlinglem1.1: |- H = ( n e. NN |-> ( ( n ^ 2 ) / ( n x. ( ( 2 x. n ) + 1 ) ) ) )
  assume stirlinglem1.2: |- F = ( n e. NN |-> ( 1 - ( 1 / ( ( 2 x. n ) + 1 ) ) ) )
  assume stirlinglem1.3: |- G = ( n e. NN |-> ( 1 / ( ( 2 x. n ) + 1 ) ) )
  assume stirlinglem1.4: |- L = ( n e. NN |-> ( 1 / n ) )


  assert |- H ~~> ( 1 / 2 )

  proof
    cH
    c1
    c2
    cdiv
    co
    #
    c1
    cmul
    co
    #
    @0
    cli
    cH
    @1
    cli
    wbr
    wtru
    c1
    @0
    vk
    cF
    cH
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    #
    wtru
    cF
    c1
    cc0
    cmin
    co
    c1
    cli
    wtru
    cc0
    c1
    vk
    cG
    cF
    c1
    cvv
    cn
    nnuz
    @2
    wtru
    cc0
    vk
    cL
    cG
    c1
    cvv
    cn
    nnuz
    @2
    cL
    cc0
    cli
    wbr
    wtru
    cL
    vn
    cn
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    cli
    stirlinglem1.4
    c1
    cc
    wcel
    @5
    cc0
    cli
    wbr
    ax-1cn
    c1
    vn
    divcnv
    ax-mp
    eqbrtri
    a1i
    cG
    cvv
    wcel
    wtru
    cG
    vn
    cn
    c1
    c2
    @3
    cmul
    co
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
    cvv
    stirlinglem1.3
    vn
    cn
    @8
    nnex
    mptex
    eqeltri
    a1i
    vk
    cv
    #
    cn
    wcel
    #
    @10
    cL
    cfv
    #
    cr
    wcel
    wtru
    @11
    @12
    c1
    @10
    cdiv
    co
    #
    cr
    @11
    vn
    @10
    @4
    @13
    cn
    cL
    crp
    cL
    @5
    wceq
    @11
    stirlinglem1.4
    a1i
    @11
    @3
    @10
    wceq
    #
    wa
    #
    @3
    @10
    c1
    cdiv
    @11
    @14
    simpr
    #
    oveq2d
    @11
    id
    #
    @11
    @10
    @10
    nnrp
    #
    rpreccld
    fvmptd
    #
    @10
    nnrecre
    eqeltrd
    adantl
    @11
    @10
    cG
    cfv
    #
    cr
    wcel
    wtru
    @11
    @20
    c1
    c2
    @10
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cr
    @11
    vn
    @10
    @8
    @23
    cn
    cG
    crp
    cG
    @9
    wceq
    @11
    stirlinglem1.3
    a1i
    @15
    @7
    @22
    c1
    cdiv
    @15
    @6
    @21
    c1
    caddc
    @15
    @3
    @10
    c2
    cmul
    @16
    oveq2d
    oveq1d
    oveq2d
    #
    @17
    @11
    @22
    @11
    @21
    @11
    c2
    @10
    c2
    cr
    wcel
    @11
    2re
    a1i
    #
    @10
    nnre
    #
    remulcld
    #
    @11
    c2
    @10
    @25
    @26
    cc0
    c2
    cle
    wbr
    @11
    0le2
    a1i
    @11
    @10
    @18
    rpge0d
    mulge0d
    ge0p1rpd
    #
    rpreccld
    #
    fvmptd
    #
    @11
    @23
    @29
    rpred
    eqeltrd
    adantl
    #
    @11
    @20
    @12
    cle
    wbr
    wtru
    @11
    @23
    @13
    @20
    @12
    cle
    @11
    @10
    @22
    c1
    @18
    @28
    @11
    1red
    #
    cc0
    c1
    cle
    wbr
    @11
    0le1
    a1i
    @11
    @10
    @22
    @26
    @11
    @21
    c1
    @27
    @32
    readdcld
    #
    @11
    @10
    @21
    @22
    @26
    @27
    @33
    @11
    c1
    @10
    cmul
    co
    @10
    @21
    clt
    @11
    @10
    @10
    nncn
    #
    mulid2d
    @11
    c1
    c2
    @10
    @32
    @25
    @18
    c1
    c2
    clt
    wbr
    @11
    1lt2
    a1i
    ltmul1dd
    eqbrtrrd
    @11
    @21
    @27
    ltp1d
    lttrd
    ltled
    lediv2ad
    @30
    @19
    3brtr4d
    adantl
    @11
    cc0
    @20
    cle
    wbr
    wtru
    @11
    cc0
    @23
    @20
    cle
    @11
    @23
    @29
    rpge0d
    @30
    breqtrrd
    adantl
    climsqz2
    wtru
    1cnd
    #
    cF
    cvv
    wcel
    wtru
    cF
    vn
    cn
    c1
    @8
    cmin
    co
    #
    cmpt
    #
    cvv
    stirlinglem1.2
    vn
    cn
    @36
    nnex
    mptex
    eqeltri
    a1i
    wtru
    @11
    wa
    @20
    @31
    recnd
    @11
    @10
    cF
    cfv
    #
    c1
    @20
    cmin
    co
    #
    wceq
    wtru
    @11
    @38
    c1
    @23
    cmin
    co
    #
    @39
    @11
    vn
    @10
    @36
    @40
    cn
    cF
    cc
    cF
    @37
    wceq
    @11
    stirlinglem1.2
    a1i
    @15
    @8
    @23
    c1
    cmin
    @24
    oveq2d
    #
    @17
    @11
    c1
    @23
    @11
    1cnd
    #
    @11
    @22
    @11
    @21
    c1
    @11
    c2
    @10
    @11
    2cnd
    @34
    mulcld
    @42
    addcld
    @11
    @22
    @28
    rpne0d
    reccld
    subcld
    #
    fvmptd
    #
    @11
    @23
    @20
    c1
    cmin
    @11
    @20
    @23
    @30
    eqcomd
    oveq2d
    eqtrd
    adantl
    climsubc2
    1m0e1
    syl6breq
    wtru
    c1
    @35
    halfcld
    cH
    cvv
    wcel
    wtru
    cH
    vn
    cn
    @3
    c2
    cexp
    co
    #
    @3
    @7
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cvv
    stirlinglem1.1
    vn
    cn
    @47
    nnex
    mptex
    eqeltri
    a1i
    @11
    @38
    cc
    wcel
    wtru
    @11
    @38
    @40
    cc
    @44
    @43
    eqeltrd
    adantl
    @11
    @10
    cH
    cfv
    #
    @0
    @38
    cmul
    co
    #
    wceq
    wtru
    @11
    @49
    @0
    @40
    cmul
    co
    #
    @50
    @11
    vn
    @10
    @0
    @36
    cmul
    co
    #
    @51
    cn
    cH
    cc
    cH
    vn
    cn
    @52
    cmpt
    #
    wceq
    @11
    cH
    @48
    @53
    stirlinglem1.1
    vn
    cn
    @47
    @52
    @3
    cn
    wcel
    #
    @47
    c1
    @45
    cmul
    co
    #
    c2
    @45
    @3
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    @0
    @45
    @57
    cdiv
    co
    #
    cmul
    co
    @52
    @54
    @45
    @55
    @46
    @58
    cdiv
    @54
    @55
    @45
    @54
    @45
    @54
    @3
    @3
    nncn
    #
    sqcld
    #
    mulid2d
    eqcomd
    @54
    @46
    @3
    @6
    cmul
    co
    #
    @3
    c1
    cmul
    co
    #
    caddc
    co
    c2
    @45
    cmul
    co
    #
    @3
    caddc
    co
    #
    @58
    @54
    @3
    @6
    c1
    @60
    @54
    c2
    @3
    @54
    2cnd
    #
    @60
    mulcld
    @54
    1cnd
    #
    adddid
    @54
    @62
    @64
    @63
    @3
    caddc
    @54
    @62
    c2
    @3
    @3
    cmul
    co
    #
    cmul
    co
    @64
    @54
    @3
    c2
    @3
    @60
    @66
    @60
    mul12d
    @54
    @68
    @45
    c2
    cmul
    @54
    @45
    @68
    @54
    @3
    @60
    sqvald
    eqcomd
    oveq2d
    eqtrd
    @54
    @3
    @60
    mulid1d
    oveq12d
    @54
    @65
    @64
    c2
    @56
    cmul
    co
    #
    caddc
    co
    @58
    @54
    @3
    @69
    @64
    caddc
    @54
    @69
    @3
    @54
    @3
    c2
    @60
    @66
    c2
    cc0
    wne
    @54
    2ne0
    a1i
    #
    divcan2d
    eqcomd
    oveq2d
    @54
    c2
    @45
    @56
    @66
    @61
    @54
    @3
    @60
    halfcld
    #
    adddid
    eqtr4d
    3eqtrd
    oveq12d
    @54
    c1
    c2
    @45
    @57
    @67
    @66
    @61
    @54
    @45
    @56
    @61
    @71
    addcld
    #
    @70
    @54
    @57
    @54
    @45
    @56
    @54
    @3
    c2
    @3
    nnrp
    #
    c2
    cz
    wcel
    @54
    2z
    a1i
    #
    rpexpcld
    @54
    @3
    @73
    rphalfcld
    rpaddcld
    rpne0d
    #
    divmuldivd
    @54
    @59
    @36
    @0
    cmul
    @54
    @59
    c1
    @56
    @57
    cdiv
    co
    #
    cmin
    co
    #
    @36
    @54
    @59
    @57
    @56
    cmin
    co
    #
    @57
    cdiv
    co
    @57
    @57
    cdiv
    co
    #
    @76
    cmin
    co
    @77
    @54
    @45
    @78
    @57
    cdiv
    @54
    @78
    @45
    @54
    @45
    @56
    @61
    @71
    pncand
    eqcomd
    oveq1d
    @54
    @57
    @56
    @57
    @72
    @71
    @72
    @75
    divsubdird
    @54
    @79
    c1
    @76
    cmin
    @54
    @57
    @72
    @75
    dividd
    oveq1d
    3eqtrd
    @54
    @76
    @8
    c1
    cmin
    @54
    @56
    c2
    @3
    cdiv
    co
    #
    cmul
    co
    #
    @57
    @80
    cmul
    co
    #
    cdiv
    co
    @76
    @8
    @54
    @56
    @57
    @80
    @71
    @72
    @54
    c2
    @3
    @66
    @60
    @3
    nnne0
    #
    divcld
    #
    @75
    @54
    c2
    @3
    @66
    @60
    @70
    @83
    divne0d
    divcan5rd
    @54
    @81
    c1
    @82
    @7
    cdiv
    @54
    @3
    c2
    @60
    @66
    @83
    @70
    divcan6d
    #
    @54
    @82
    @45
    @80
    cmul
    co
    #
    @81
    caddc
    co
    @7
    @54
    @45
    @56
    @80
    @61
    @71
    @84
    adddird
    @54
    @86
    @6
    @81
    c1
    caddc
    @54
    @86
    c2
    @45
    @3
    cdiv
    co
    #
    cmul
    co
    @6
    @54
    @45
    c2
    @3
    @61
    @66
    @60
    @83
    div12d
    @54
    @87
    @3
    c2
    cmul
    @54
    @3
    @87
    @54
    @3
    c1
    cexp
    co
    @3
    c2
    c1
    cmin
    co
    #
    cexp
    co
    @3
    @87
    c1
    @88
    @3
    cexp
    1e2m1
    oveq2i
    @54
    @3
    @60
    exp1d
    @54
    @3
    c2
    @60
    @83
    @74
    expm1d
    3eqtr3a
    eqcomd
    oveq2d
    eqtrd
    @85
    oveq12d
    eqtrd
    oveq12d
    eqtr3d
    oveq2d
    eqtrd
    oveq2d
    3eqtr2d
    mpteq2ia
    eqtri
    a1i
    @15
    @36
    @40
    @0
    cmul
    @41
    oveq2d
    @17
    @11
    @0
    @40
    @11
    c1
    @42
    halfcld
    @43
    mulcld
    fvmptd
    @11
    @38
    @40
    @0
    cmul
    @44
    oveq2d
    eqtr4d
    adantl
    climmulc2
    trud
    @0
    halfcn
    mulid1i
    breqtri
end
