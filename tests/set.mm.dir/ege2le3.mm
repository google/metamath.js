include "c2.mm"
include "ceu.mm"
include "cle.mm"
include "wbr.mm"
include "c3.mm"
include "wtru.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cfv.mm"
include "co.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0nn0.mm"
include "1e0p1.mm"
include "0z.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cfa.mm"
include "cdiv.mm"
include "fveq2.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "ax-1cn.mm"
include "div1i.mm"
include "1ex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "seq1i.mm"
include "1nn0.mm"
include "fac1.mm"
include "seqp1i.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "a1i.mm"
include "ce.mm"
include "cli.mm"
include "cc.mm"
include "cmpt.mm"
include "cexp.mm"
include "cz.mm"
include "nn0z.mm"
include "1exp.mm"
include "syl.mm"
include "oveq1d.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "efcvg.mm"
include "df-e.mm"
include "syl6breqr.mm"
include "wa.mm"
include "cr.mm"
include "ovex.mm"
include "adantl.mm"
include "cn.mm"
include "faccl.mm"
include "nnrecred.mm"
include "eqeltrd.mm"
include "clt.mm"
include "nnred.mm"
include "nngt0d.mm"
include "1re.mm"
include "0le1.mm"
include "divge0.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "climserle.mm"
include "eqbrtrrd.mm"
include "trud.mm"
include "cmin.mm"
include "nnuz.mm"
include "1zzd.mm"
include "recnd.mm"
include "clim2ser.mm"
include "0p1e1.mm"
include "seqeq1.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "3brtr3g.mm"
include "cmul.mm"
include "2cnd.mm"
include "oveq2.mm"
include "eqid.mm"
include "halfre.mm"
include "simpr.mm"
include "reexpcl.mm"
include "sylancr.mm"
include "cabs.mm"
include "1lt2.mm"
include "2re.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "breqtrri.mm"
include "georeclim.mm"
include "2m1e1.mm"
include "2cn.mm"
include "eqtri.mm"
include "syl6breq.mm"
include "halfcn.mm"
include "exp0.mm"
include "nnnn0.mm"
include "sylan2.mm"
include "eqtr4d.mm"
include "isermulc2.mm"
include "2t1e2.mm"
include "remulcl.mm"
include "faclbnd2.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "nnrpd.mm"
include "rphalfcld.mm"
include "lerecd.mm"
include "mpbid.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divrecd.mm"
include "wne.mm"
include "2ne0.mm"
include "recdiv.mm"
include "mpanr12.mm"
include "exprecd.mm"
include "3eqtr4rd.mm"
include "3brtr4d.mm"
include "iserle.mm"
include "ere.mm"
include "lesubaddi.mm"
include "mpbi.mm"
include "df-3.mm"
include "pm3.2i.mm"

theorem ege2le3
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vk: setvar k
  assume erelem1.1: |- F = ( n e. NN |-> ( 2 x. ( ( 1 / 2 ) ^ n ) ) )
  assume erelem1.2: |- G = ( n e. NN0 |-> ( 1 / ( ! ` n ) ) )


  assert |- ( 2 <_ _e /\ _e <_ 3 )

  proof
    c2
    ceu
    cle
    wbr
    #
    ceu
    c3
    cle
    wbr
    @0
    wtru
    c1
    caddc
    cG
    cc0
    cseq
    #
    cfv
    #
    c2
    ceu
    cle
    wtru
    @2
    c1
    c1
    caddc
    co
    c2
    wtru
    c1
    c1
    caddc
    cG
    c1
    cc0
    cc0
    cn0
    nn0uz
    0nn0
    1e0p1
    wtru
    c1
    caddc
    cG
    cc0
    0z
    cc0
    cn0
    wcel
    #
    cc0
    cG
    cfv
    c1
    wceq
    wtru
    0nn0
    vn
    cc0
    c1
    vn
    cv
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    c1
    cn0
    cG
    @4
    cc0
    wceq
    #
    @6
    c1
    c1
    cdiv
    co
    #
    c1
    @7
    @5
    c1
    c1
    cdiv
    @7
    @5
    cc0
    cfa
    cfv
    c1
    @4
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    oveq2d
    c1
    ax-1cn
    div1i
    #
    syl6eq
    erelem1.2
    1ex
    fvmpt
    mp1i
    seq1i
    #
    c1
    cn0
    wcel
    #
    c1
    cG
    cfv
    c1
    wceq
    wtru
    1nn0
    vn
    c1
    @6
    c1
    cn0
    cG
    @4
    c1
    wceq
    #
    @6
    @8
    c1
    @12
    @5
    c1
    c1
    cdiv
    @12
    @5
    c1
    cfa
    cfv
    c1
    @4
    c1
    cfa
    fveq2
    fac1
    syl6eq
    oveq2d
    @9
    syl6eq
    erelem1.2
    1ex
    fvmpt
    mp1i
    seqp1i
    df-2
    syl6eqr
    wtru
    ceu
    vk
    cG
    cc0
    c1
    cn0
    nn0uz
    @11
    wtru
    1nn0
    a1i
    wtru
    @1
    c1
    ce
    cfv
    #
    ceu
    cli
    c1
    cc
    wcel
    @1
    @13
    cli
    wbr
    wtru
    ax-1cn
    c1
    vn
    cG
    cG
    vn
    cn0
    @6
    cmpt
    vn
    cn0
    c1
    @4
    cexp
    co
    #
    @5
    cdiv
    co
    #
    cmpt
    erelem1.2
    vn
    cn0
    @15
    @6
    @4
    cn0
    wcel
    #
    @14
    c1
    @5
    cdiv
    @16
    @4
    cz
    wcel
    @14
    c1
    wceq
    @4
    nn0z
    @4
    1exp
    syl
    oveq1d
    mpteq2ia
    eqtr4i
    efcvg
    mp1i
    df-e
    syl6breqr
    #
    wtru
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @18
    cG
    cfv
    #
    c1
    @18
    cfa
    cfv
    #
    cdiv
    co
    #
    cr
    @19
    @21
    @23
    wceq
    #
    wtru
    vn
    @18
    @6
    @23
    cn0
    cG
    @4
    @18
    wceq
    #
    @5
    @22
    c1
    cdiv
    @4
    @18
    cfa
    fveq2
    oveq2d
    erelem1.2
    c1
    @22
    cdiv
    ovex
    fvmpt
    adantl
    #
    @20
    @22
    @19
    @22
    cn
    wcel
    wtru
    @18
    faccl
    adantl
    #
    nnrecred
    eqeltrd
    #
    @20
    cc0
    @23
    @21
    cle
    @20
    @22
    cr
    wcel
    #
    cc0
    @22
    clt
    wbr
    #
    cc0
    @23
    cle
    wbr
    #
    @20
    @22
    @27
    nnred
    @20
    @22
    @27
    nngt0d
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @29
    @30
    wa
    @31
    1re
    0le1
    c1
    @22
    divge0
    mpanl12
    syl2anc
    @26
    breqtrrd
    climserle
    eqbrtrrd
    trud
    ceu
    c2
    c1
    caddc
    co
    #
    c3
    cle
    ceu
    c1
    cmin
    co
    #
    c2
    cle
    wbr
    #
    ceu
    @32
    cle
    wbr
    @34
    wtru
    @33
    c2
    vk
    cG
    cF
    c1
    cn
    nnuz
    wtru
    1zzd
    #
    wtru
    caddc
    cG
    cc0
    c1
    caddc
    co
    #
    cseq
    #
    ceu
    cc0
    @1
    cfv
    #
    cmin
    co
    caddc
    cG
    c1
    cseq
    #
    @33
    cli
    wtru
    ceu
    vk
    cG
    cc0
    cc0
    cn0
    nn0uz
    @3
    wtru
    0nn0
    a1i
    #
    @20
    @21
    @28
    recnd
    @17
    clim2ser
    @36
    c1
    wceq
    #
    @37
    @39
    wceq
    0p1e1
    caddc
    cG
    @36
    c1
    seqeq1
    ax-mp
    @38
    c1
    ceu
    cmin
    @38
    c1
    wceq
    @10
    trud
    oveq2i
    3brtr3g
    wtru
    caddc
    cF
    c1
    cseq
    c2
    c1
    cmul
    co
    c2
    cli
    wtru
    c1
    c2
    vk
    vn
    cn0
    c1
    c2
    cdiv
    co
    #
    @4
    cexp
    co
    #
    cmpt
    #
    cF
    c1
    cn
    nnuz
    @35
    wtru
    2cnd
    #
    wtru
    caddc
    @44
    @36
    cseq
    #
    c2
    cc0
    caddc
    @44
    cc0
    cseq
    #
    cfv
    #
    cmin
    co
    #
    caddc
    @44
    c1
    cseq
    #
    c1
    cli
    wtru
    c2
    vk
    @44
    cc0
    cc0
    cn0
    nn0uz
    @40
    @20
    @18
    @44
    cfv
    #
    @42
    @18
    cexp
    co
    #
    cc
    @19
    @51
    @52
    wceq
    #
    wtru
    vn
    @18
    @43
    @52
    cn0
    @44
    @4
    @18
    @42
    cexp
    oveq2
    #
    @44
    eqid
    #
    @42
    @18
    cexp
    ovex
    fvmpt
    adantl
    #
    @20
    @52
    @20
    @42
    cr
    wcel
    @19
    @52
    cr
    wcel
    #
    halfre
    wtru
    @19
    simpr
    #
    @42
    @18
    reexpcl
    sylancr
    #
    recnd
    eqeltrd
    #
    wtru
    @47
    c2
    c2
    c1
    cmin
    co
    #
    cdiv
    co
    #
    c2
    cli
    wtru
    c2
    vk
    @44
    @45
    c1
    c2
    cabs
    cfv
    #
    clt
    wbr
    wtru
    c1
    c2
    @63
    clt
    1lt2
    c2
    cr
    wcel
    #
    cc0
    c2
    cle
    wbr
    @63
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    breqtrri
    a1i
    @56
    georeclim
    @62
    c2
    c1
    cdiv
    co
    c2
    @61
    c1
    c2
    cdiv
    2m1e1
    oveq2i
    c2
    2cn
    div1i
    eqtri
    syl6breq
    clim2ser
    @41
    @46
    @50
    wceq
    0p1e1
    caddc
    @44
    @36
    c1
    seqeq1
    ax-mp
    @49
    @61
    c1
    @48
    c1
    c2
    cmin
    @48
    c1
    wceq
    wtru
    c1
    caddc
    @44
    cc0
    0z
    cc0
    @44
    cfv
    #
    c1
    wceq
    wtru
    @65
    @42
    cc0
    cexp
    co
    #
    c1
    @3
    @65
    @66
    wceq
    0nn0
    vn
    cc0
    @43
    @66
    cn0
    @44
    @4
    cc0
    @42
    cexp
    oveq2
    @55
    @42
    cc0
    cexp
    ovex
    fvmpt
    ax-mp
    @42
    cc
    wcel
    @66
    c1
    wceq
    halfcn
    @42
    exp0
    ax-mp
    eqtri
    a1i
    seq1i
    trud
    oveq2i
    2m1e1
    eqtri
    3brtr3g
    @18
    cn
    wcel
    #
    wtru
    @19
    @51
    cc
    wcel
    @18
    nnnn0
    #
    @60
    sylan2
    wtru
    @67
    wa
    #
    @18
    cF
    cfv
    #
    c2
    @52
    cmul
    co
    #
    c2
    @51
    cmul
    co
    @67
    @70
    @71
    wceq
    wtru
    vn
    @18
    c2
    @43
    cmul
    co
    @71
    cn
    cF
    @25
    @43
    @52
    c2
    cmul
    @54
    oveq2d
    erelem1.1
    c2
    @52
    cmul
    ovex
    fvmpt
    adantl
    #
    @69
    @51
    @52
    c2
    cmul
    @67
    wtru
    @19
    @53
    @68
    @56
    sylan2
    oveq2d
    eqtr4d
    isermulc2
    2t1e2
    syl6breq
    @67
    wtru
    @19
    @21
    cr
    wcel
    @68
    @28
    sylan2
    @69
    @70
    @71
    cr
    @72
    @67
    wtru
    @19
    @71
    cr
    wcel
    #
    @68
    @20
    @64
    @57
    @73
    2re
    @59
    c2
    @52
    remulcl
    sylancr
    sylan2
    eqeltrd
    @69
    @23
    @71
    @21
    @70
    cle
    @67
    wtru
    @19
    @23
    @71
    cle
    wbr
    @68
    @20
    @23
    c1
    c2
    @18
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cdiv
    co
    #
    @71
    cle
    @20
    @75
    @22
    cle
    wbr
    #
    @23
    @76
    cle
    wbr
    @19
    @77
    wtru
    @18
    faclbnd2
    adantl
    @20
    @75
    @22
    @20
    @74
    @20
    @74
    @20
    c2
    cn
    wcel
    @19
    @74
    cn
    wcel
    2nn
    @58
    c2
    @18
    nnexpcl
    sylancr
    #
    nnrpd
    rphalfcld
    @20
    @22
    @27
    nnrpd
    lerecd
    mpbid
    @20
    c2
    @74
    cdiv
    co
    #
    c2
    c1
    @74
    cdiv
    co
    #
    cmul
    co
    @76
    @71
    @20
    c2
    @74
    @20
    2cnd
    #
    @20
    @74
    @78
    nncnd
    #
    @20
    @74
    @78
    nnne0d
    #
    divrecd
    @20
    @74
    cc
    wcel
    #
    @74
    cc0
    wne
    #
    @76
    @79
    wceq
    #
    @82
    @83
    @84
    @85
    wa
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    @86
    2cn
    2ne0
    @74
    c2
    recdiv
    mpanr12
    syl2anc
    @20
    @52
    @80
    c2
    cmul
    @20
    c2
    @18
    @81
    @87
    @20
    2ne0
    a1i
    @19
    @18
    cz
    wcel
    wtru
    @18
    nn0z
    adantl
    exprecd
    oveq2d
    3eqtr4rd
    breqtrrd
    sylan2
    @67
    wtru
    @19
    @24
    @68
    @26
    sylan2
    @72
    3brtr4d
    iserle
    trud
    ceu
    c1
    c2
    ere
    1re
    2re
    lesubaddi
    mpbi
    df-3
    breqtrri
    pm3.2i
end
