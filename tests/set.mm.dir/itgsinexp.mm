include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "c2.mm"
include "caddc.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "cc.mm"
include "eluzelz.mm"
include "zcn.mm"
include "3syl.mm"
include "1cnd.mm"
include "npcand.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cn.mm"
include "uz2m1nn.mm"
include "syl.mm"
include "nncnd.mm"
include "cc0.mm"
include "cpi.mm"
include "cioo.mm"
include "cv.mm"
include "csin.mm"
include "cexp.mm"
include "citg.mm"
include "cn0.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "oveq2.mm"
include "ad2antlr.mm"
include "itgeq2dv.mm"
include "2cnd.mm"
include "npcan.mm"
include "syl2anc.mm"
include "uznn0sub.mm"
include "2nn0.mm"
include "nn0addcld.mm"
include "eqeltrd.mm"
include "itgex.mm"
include "fvmptd.mm"
include "ioosscn.mm"
include "sseli.mm"
include "sincld.mm"
include "adantl.mm"
include "adantr.mm"
include "expcld.mm"
include "cicc.mm"
include "wss.mm"
include "ioossicc.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "cr.mm"
include "0re.mm"
include "pire.mm"
include "iccssre.mm"
include "mp2an.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ccncf.mm"
include "cibl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "mpteq2dva.mm"
include "nfmpt1.mm"
include "nfcv.mm"
include "sincn.mm"
include "expcnfg.mm"
include "cncfmptss.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "iblss.mm"
include "itgcl.mm"
include "adddirp1d.mm"
include "clt.mm"
include "wbr.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "expm1t.mm"
include "syl2anr.mm"
include "ccos.mm"
include "cneg.mm"
include "itgsinexplem1.mm"
include "subsub4d.mm"
include "1p1e2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "sincossq.mm"
include "sincl.mm"
include "sqcld.mm"
include "coscl.mm"
include "subaddd.mm"
include "mpbird.mm"
include "nnm1nn0.mm"
include "subdird.mm"
include "mulid2d.mm"
include "expaddd.mm"
include "pncan3d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "itgsub.mm"
include "3eqtrd.mm"
include "subdid.mm"
include "3eqtr2d.mm"
include "mulcld.mm"
include "mpbid.mm"
include "nnne0d.mm"
include "divcan3d.mm"
include "div23d.mm"
include "3eqtr3d.mm"

theorem itgsinexp
  let wph: wff ph
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cN: class N
  let vk: setvar k
  assume itgsinexp.1: |- I = ( n e. NN0 |-> S. ( 0 (,) _pi ) ( ( sin ` x ) ^ n ) _d x )
  assume itgsinexp.2: |- ( ph -> N e. ( ZZ>= ` 2 ) )

  disjoint n x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( I ` N ) = ( ( ( N - 1 ) / N ) x. ( I ` ( N - 2 ) ) ) )

  proof
    wph
    cN
    cN
    cI
    cfv
    #
    cmul
    co
    #
    cN
    cdiv
    co
    cN
    c1
    cmin
    co
    #
    cN
    c2
    cmin
    co
    #
    cI
    cfv
    #
    cmul
    co
    #
    cN
    cdiv
    co
    @0
    @2
    cN
    cdiv
    co
    @4
    cmul
    co
    wph
    @1
    @5
    cN
    cdiv
    wph
    @1
    @2
    c1
    caddc
    co
    #
    @0
    cmul
    co
    @2
    @0
    cmul
    co
    #
    @0
    caddc
    co
    #
    @5
    wph
    cN
    @6
    @0
    cmul
    wph
    @6
    cN
    wph
    cN
    c1
    wph
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    cN
    cc
    wcel
    #
    itgsinexp.2
    c2
    cN
    eluzelz
    cN
    zcn
    3syl
    #
    wph
    1cnd
    #
    npcand
    eqcomd
    oveq1d
    wph
    @2
    @0
    wph
    @2
    wph
    @9
    @2
    cn
    wcel
    #
    itgsinexp.2
    cN
    uz2m1nn
    syl
    #
    nncnd
    #
    wph
    @0
    vx
    cc0
    cpi
    cioo
    co
    #
    vx
    cv
    #
    csin
    cfv
    #
    cN
    cexp
    co
    #
    citg
    #
    cc
    wph
    vn
    cN
    vx
    @16
    @18
    vn
    cv
    #
    cexp
    co
    #
    citg
    #
    @20
    cn0
    cI
    cvv
    cI
    vn
    cn0
    @23
    cmpt
    wceq
    wph
    itgsinexp.1
    a1i
    #
    wph
    @21
    cN
    wceq
    #
    wa
    vx
    @16
    @22
    @19
    @25
    @22
    @19
    wceq
    wph
    @17
    @16
    wcel
    #
    @21
    cN
    @18
    cexp
    oveq2
    ad2antlr
    itgeq2dv
    wph
    cN
    @3
    c2
    caddc
    co
    #
    cn0
    wph
    @10
    c2
    cc
    wcel
    #
    cN
    @27
    wceq
    @11
    wph
    2cnd
    #
    @10
    @28
    wa
    @27
    cN
    cN
    c2
    npcan
    eqcomd
    syl2anc
    wph
    @3
    c2
    wph
    @9
    @3
    cn0
    wcel
    #
    itgsinexp.2
    c2
    cN
    uznn0sub
    syl
    c2
    cn0
    wcel
    #
    wph
    2nn0
    a1i
    nn0addcld
    eqeltrd
    #
    @20
    cvv
    wcel
    wph
    vx
    @16
    @19
    itgex
    a1i
    fvmptd
    #
    wph
    vx
    @16
    @19
    cc
    wph
    @26
    wa
    #
    @18
    cN
    @26
    @18
    cc
    wcel
    #
    wph
    @26
    @17
    @16
    cc
    @17
    cc0
    cpi
    ioosscn
    sseli
    #
    sincld
    #
    adantl
    #
    wph
    cN
    cn0
    wcel
    #
    @26
    @32
    adantr
    expcld
    #
    wph
    vx
    @16
    cc0
    cpi
    cicc
    co
    #
    @19
    cc
    @16
    @41
    wss
    wph
    cc0
    cpi
    ioossicc
    a1i
    #
    @16
    cvol
    cdm
    wcel
    wph
    cc0
    cpi
    ioombl
    a1i
    #
    wph
    @17
    @41
    wcel
    #
    wa
    #
    @18
    cN
    @44
    @35
    wph
    @44
    @17
    @41
    cc
    @17
    @41
    cr
    cc
    cc0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @41
    cr
    wss
    0re
    pire
    cc0
    cpi
    iccssre
    mp2an
    ax-resscn
    sstri
    #
    sseli
    #
    sincld
    adantl
    #
    wph
    @39
    @44
    @32
    adantr
    expcld
    #
    wph
    @46
    @47
    vx
    @41
    @19
    cmpt
    #
    @41
    cc
    ccncf
    co
    #
    wcel
    @52
    cibl
    wcel
    @46
    wph
    0re
    a1i
    #
    @47
    wph
    pire
    a1i
    #
    wph
    @52
    vx
    @41
    @17
    vx
    cc
    @19
    cmpt
    #
    cfv
    #
    cmpt
    @53
    wph
    vx
    @41
    @19
    @57
    @45
    @57
    @19
    @45
    @17
    cc
    wcel
    #
    @19
    cc
    wcel
    @57
    @19
    wceq
    @44
    @58
    wph
    @49
    adantl
    #
    @51
    vx
    cc
    @19
    cc
    @56
    @56
    eqid
    fvmpt2
    syl2anc
    eqcomd
    mpteq2dva
    wph
    vx
    cc
    cc
    @41
    @56
    vx
    cc
    @19
    nfmpt1
    wph
    vx
    cc
    csin
    cN
    vx
    csin
    nfcv
    #
    csin
    cc
    cc
    ccncf
    co
    wcel
    wph
    sincn
    a1i
    #
    @32
    expcnfg
    @41
    cc
    wss
    wph
    @48
    a1i
    #
    cncfmptss
    eqeltrd
    cc0
    cpi
    @52
    cniccibl
    syl3anc
    iblss
    #
    itgcl
    eqeltrd
    #
    adddirp1d
    wph
    @5
    @7
    cmin
    co
    #
    @0
    wceq
    @8
    @5
    wceq
    wph
    @0
    @65
    wph
    @0
    @2
    vx
    @16
    @18
    @3
    cexp
    co
    #
    citg
    #
    @20
    cmin
    co
    #
    cmul
    co
    #
    @2
    @4
    @0
    cmin
    co
    #
    cmul
    co
    @65
    wph
    @0
    @20
    vx
    @16
    @18
    @2
    cexp
    co
    #
    @18
    cmul
    co
    #
    citg
    #
    @69
    @33
    wph
    vx
    @16
    @19
    @72
    @26
    @35
    cN
    cn
    wcel
    #
    @19
    @72
    wceq
    wph
    @37
    wph
    @74
    c1
    cN
    clt
    wbr
    #
    wph
    @9
    @74
    @75
    wa
    itgsinexp.2
    cN
    eluz2b2
    sylib
    simpld
    #
    @18
    cN
    expm1t
    syl2anr
    itgeq2dv
    wph
    @73
    @2
    vx
    @16
    @17
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    @18
    @2
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    citg
    #
    cmul
    co
    @2
    vx
    @16
    @78
    @66
    cmul
    co
    #
    citg
    #
    cmul
    co
    @69
    wph
    vx
    vx
    cc
    @71
    cmpt
    #
    vx
    cc
    @77
    cneg
    #
    cmpt
    #
    vx
    cc
    @2
    @80
    cmul
    co
    @77
    cmul
    co
    #
    cmpt
    #
    vx
    cc
    @72
    cmpt
    #
    vx
    cc
    @88
    @86
    cmul
    co
    cmpt
    #
    vx
    cc
    @81
    cmpt
    #
    @2
    @85
    eqid
    @87
    eqid
    @89
    eqid
    @90
    eqid
    @91
    eqid
    @92
    eqid
    @14
    itgsinexplem1
    wph
    @82
    @84
    @2
    cmul
    wph
    vx
    @16
    @81
    @83
    @34
    @80
    @66
    @78
    cmul
    @34
    @79
    @3
    @18
    cexp
    wph
    @79
    @3
    wceq
    @26
    wph
    @79
    cN
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @3
    wph
    cN
    c1
    c1
    @11
    @12
    @12
    subsub4d
    wph
    @93
    c2
    cN
    cmin
    @93
    c2
    wceq
    wph
    1p1e2
    a1i
    oveq2d
    eqtrd
    #
    adantr
    oveq2d
    oveq2d
    itgeq2dv
    oveq2d
    wph
    @84
    @68
    @2
    cmul
    wph
    @84
    vx
    @16
    c1
    @18
    c2
    cexp
    co
    #
    cmin
    co
    #
    @66
    cmul
    co
    #
    citg
    vx
    @16
    @66
    @19
    cmin
    co
    #
    citg
    @68
    wph
    vx
    @16
    @83
    @97
    @26
    @83
    @97
    wceq
    wph
    @26
    @78
    @96
    @66
    cmul
    @26
    @58
    @78
    @96
    wceq
    @36
    @58
    @96
    @78
    @58
    @96
    @78
    wceq
    @95
    @78
    caddc
    co
    c1
    wceq
    @17
    sincossq
    @58
    c1
    @95
    @78
    @58
    1cnd
    @58
    @18
    @17
    sincl
    sqcld
    @58
    @77
    @17
    coscl
    sqcld
    subaddd
    mpbird
    eqcomd
    syl
    oveq1d
    adantl
    itgeq2dv
    wph
    vx
    @16
    @97
    @98
    @34
    @97
    c1
    @66
    cmul
    co
    #
    @95
    @66
    cmul
    co
    #
    cmin
    co
    @98
    @34
    c1
    @95
    @66
    @34
    1cnd
    @26
    @95
    cc
    wcel
    wph
    @26
    @18
    @37
    sqcld
    adantl
    @34
    @18
    @3
    @38
    wph
    @30
    @26
    wph
    @3
    @79
    cn0
    wph
    @79
    @3
    @94
    eqcomd
    wph
    @13
    @79
    cn0
    wcel
    @14
    @2
    nnm1nn0
    syl
    eqeltrd
    #
    adantr
    #
    expcld
    #
    subdird
    @34
    @99
    @66
    @100
    @19
    cmin
    @34
    @66
    @103
    mulid2d
    @34
    @18
    c2
    @3
    caddc
    co
    #
    cexp
    co
    #
    @100
    @19
    @34
    @18
    c2
    @3
    @38
    @102
    @31
    @34
    2nn0
    a1i
    expaddd
    wph
    @105
    @19
    wceq
    @26
    wph
    @104
    cN
    @18
    cexp
    wph
    c2
    cN
    @29
    @11
    pncan3d
    oveq2d
    adantr
    eqtr3d
    oveq12d
    eqtrd
    itgeq2dv
    wph
    vx
    @16
    @66
    @19
    cc
    @103
    wph
    vx
    @16
    @41
    @66
    cc
    @42
    @43
    @45
    @18
    @3
    @50
    wph
    @30
    @44
    @101
    adantr
    expcld
    #
    wph
    @46
    @47
    vx
    @41
    @66
    cmpt
    #
    @53
    wcel
    @107
    cibl
    wcel
    @54
    @55
    wph
    @107
    vx
    @41
    @17
    vx
    cc
    @66
    cmpt
    #
    cfv
    #
    cmpt
    @53
    wph
    vx
    @41
    @66
    @109
    @45
    @109
    @66
    @45
    @58
    @66
    cc
    wcel
    @109
    @66
    wceq
    @59
    @106
    vx
    cc
    @66
    cc
    @108
    @108
    eqid
    fvmpt2
    syl2anc
    eqcomd
    mpteq2dva
    wph
    vx
    cc
    cc
    @41
    @108
    vx
    cc
    @66
    nfmpt1
    wph
    vx
    cc
    csin
    @3
    @60
    @61
    @101
    expcnfg
    @62
    cncfmptss
    eqeltrd
    cc0
    cpi
    @107
    cniccibl
    syl3anc
    iblss
    #
    @40
    @63
    itgsub
    3eqtrd
    oveq2d
    3eqtrd
    3eqtrd
    wph
    @70
    @68
    @2
    cmul
    wph
    @4
    @67
    @0
    @20
    cmin
    wph
    vn
    @3
    @23
    @67
    cn0
    cI
    cvv
    @24
    @21
    @3
    wceq
    #
    @23
    @67
    wceq
    wph
    @111
    vx
    @16
    @22
    @66
    @111
    @22
    @66
    wceq
    @26
    @21
    @3
    @18
    cexp
    oveq2
    adantr
    itgeq2dv
    adantl
    @101
    @67
    cvv
    wcel
    wph
    vx
    @16
    @66
    itgex
    a1i
    fvmptd
    #
    @33
    oveq12d
    oveq2d
    wph
    @2
    @4
    @0
    @15
    wph
    @4
    @67
    cc
    @112
    wph
    vx
    @16
    @66
    cc
    @103
    @110
    itgcl
    eqeltrd
    #
    @64
    subdid
    3eqtr2d
    eqcomd
    wph
    @5
    @7
    @0
    wph
    @2
    @4
    @15
    @113
    mulcld
    wph
    @2
    @0
    @15
    @64
    mulcld
    @64
    subaddd
    mpbid
    3eqtrd
    oveq1d
    wph
    @0
    cN
    @64
    @11
    wph
    cN
    @76
    nnne0d
    #
    divcan3d
    wph
    @2
    @4
    cN
    @15
    @113
    @11
    @114
    div23d
    3eqtr3d
end
