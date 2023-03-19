include "co.mm"
include "ccph.mm"
include "wcel.mm"
include "cc.mm"
include "chl.mm"
include "hlcph.mm"
include "syl.mm"
include "wss.mm"
include "lssss.mm"
include "sseldd.mm"
include "cphipcl.mm"
include "syl3anc.mm"
include "cabs.mm"
include "cfv.mm"
include "abscld.mm"
include "recnd.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cr.mm"
include "caddc.mm"
include "clt.mm"
include "cmul.mm"
include "resqcld.mm"
include "renegcld.mm"
include "reipcl.mm"
include "syl2anc.mm"
include "2re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "c1.mm"
include "0red.mm"
include "peano2re.mm"
include "ipge0.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an23.mm"
include "df-2.mm"
include "oveq2i.mm"
include "syl6reqr.mm"
include "breqtrrd.mm"
include "lttrd.mm"
include "cdiv.mm"
include "cvsca.mm"
include "cmin.mm"
include "cv.mm"
include "wral.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "cphlmod.mm"
include "wne.mm"
include "cphl.mm"
include "hlphl.mm"
include "eqid.mm"
include "ipcl.mm"
include "hlress.mm"
include "ge0p1rpd.mm"
include "rpne0d.mm"
include "cphdivcl.mm"
include "syl13anc.mm"
include "syl5eqel.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cngp.mm"
include "cphngp.mm"
include "nmcl.mm"
include "lmodvscl.mm"
include "lmodvsubcl.mm"
include "nmge0.mm"
include "le2sqd.mm"
include "mpbid.mm"
include "subge0d.mm"
include "mpbird.mm"
include "crp.mm"
include "cz.mm"
include "2z.mm"
include "rpexpcl.mm"
include "rerpdivcld.mm"
include "remulcld.mm"
include "negcld.mm"
include "pncand.mm"
include "nmsq.mm"
include "cphsubdir.mm"
include "cphsubdi.mm"
include "oveq1d.mm"
include "subcld.mm"
include "eqeltrd.mm"
include "subsub4d.mm"
include "1cnd.mm"
include "adddid.mm"
include "oveq2d.mm"
include "ccj.mm"
include "cphassr.mm"
include "divcld.mm"
include "cjcld.mm"
include "mulcomd.mm"
include "divassd.mm"
include "absvalsqd.mm"
include "fveq2i.mm"
include "cjdivd.mm"
include "cjred.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "3eqtr4rd.mm"
include "3eqtrd.mm"
include "sqvald.mm"
include "oveq12d.mm"
include "divcan5d.mm"
include "eqtr2d.mm"
include "rpcnd.mm"
include "div23d.mm"
include "cphipcj.mm"
include "3eqtr3d.mm"
include "cph2ass.mm"
include "syl122anc.mm"
include "absdivd.mm"
include "rpge0d.mm"
include "absidd.mm"
include "sqdivd.mm"
include "pncan2.mm"
include "subdid.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"
include "negsubd.mm"
include "addcomd.mm"
include "3eqtr2d.mm"
include "mulneg2d.mm"
include "ge0divd.mm"
include "mulneg12.mm"
include "prodge02.mm"
include "le0neg1d.mm"
include "sqge0d.mm"
include "wa.mm"
include "wb.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "sqeq0d.mm"
include "abs00d.mm"

theorem pjthlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let c.xi: class .,
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.po: class .(+)
  let cO: class O
  assume pjthlem.v: |- V = ( Base ` W )
  assume pjthlem.n: |- N = ( norm ` W )
  assume pjthlem.p: |- .+ = ( +g ` W )
  assume pjthlem.m: |- .- = ( -g ` W )
  assume pjthlem.h: |- ., = ( .i ` W )
  assume pjthlem.l: |- L = ( LSubSp ` W )
  assume pjthlem.1: |- ( ph -> W e. CHil )
  assume pjthlem.2: |- ( ph -> U e. L )
  assume pjthlem.4: |- ( ph -> A e. V )
  assume pjthlem.5: |- ( ph -> B e. U )
  assume pjthlem.7: |- ( ph -> A. x e. U ( N ` A ) <_ ( N ` ( A .- x ) ) )
  assume pjthlem.8: |- T = ( ( A ., B ) / ( ( B ., B ) + 1 ) )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint N x
  disjoint ph x
  disjoint U x
  disjoint V x
  disjoint T x
  disjoint W x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .- w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint ., w
  disjoint ., z
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint .(+) x
  disjoint O x
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint .+ y
  disjoint W w
  disjoint W y
  disjoint W z
  assert |- ( ph -> ( A ., B ) = 0 )

  proof
    wph
    cA
    cB
    c.xi
    co
    #
    wph
    cW
    ccph
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    @0
    cc
    wcel
    wph
    cW
    chl
    wcel
    #
    @1
    pjthlem.1
    cW
    hlcph
    syl
    #
    pjthlem.4
    wph
    cU
    cV
    cB
    wph
    cU
    cL
    wcel
    #
    cU
    cV
    wss
    pjthlem.2
    cL
    cU
    cV
    cW
    pjthlem.v
    pjthlem.l
    lssss
    syl
    pjthlem.5
    sseldd
    #
    cA
    cB
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    cphipcl
    syl3anc
    #
    wph
    @0
    cabs
    cfv
    #
    wph
    @9
    wph
    @0
    @8
    abscld
    #
    recnd
    #
    wph
    @9
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @12
    cc0
    cle
    wbr
    #
    cc0
    @12
    cle
    wbr
    #
    wph
    @14
    cc0
    @12
    cneg
    #
    cle
    wbr
    #
    wph
    @16
    cr
    wcel
    cB
    cB
    c.xi
    co
    #
    c2
    caddc
    co
    #
    cr
    wcel
    #
    cc0
    @19
    clt
    wbr
    cc0
    @16
    @19
    cmul
    co
    #
    cle
    wbr
    @17
    wph
    @12
    wph
    @9
    @10
    resqcld
    #
    renegcld
    wph
    @18
    cr
    wcel
    #
    c2
    cr
    wcel
    @20
    wph
    @1
    @3
    @23
    @5
    @7
    cB
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    reipcl
    syl2anc
    #
    2re
    @18
    c2
    readdcl
    sylancl
    #
    wph
    cc0
    @18
    c1
    caddc
    co
    #
    @19
    wph
    0red
    #
    wph
    @23
    @26
    cr
    wcel
    @24
    @18
    peano2re
    syl
    #
    @25
    wph
    cc0
    @18
    @26
    @27
    @24
    @28
    wph
    @1
    @3
    cc0
    @18
    cle
    wbr
    @5
    @7
    cB
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    ipge0
    syl2anc
    #
    wph
    @18
    @24
    ltp1d
    lelttrd
    wph
    @26
    @26
    c1
    caddc
    co
    #
    @19
    clt
    wph
    @26
    @28
    ltp1d
    wph
    @30
    @18
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @19
    wph
    @18
    cc
    wcel
    #
    @30
    @32
    wceq
    #
    wph
    @18
    @24
    recnd
    #
    @33
    c1
    cc
    wcel
    #
    @36
    @34
    ax-1cn
    ax-1cn
    @18
    c1
    c1
    addass
    mp3an23
    syl
    c2
    @31
    @18
    caddc
    df-2
    oveq2i
    syl6reqr
    #
    breqtrrd
    lttrd
    wph
    cc0
    @12
    @19
    cneg
    #
    cmul
    co
    #
    @21
    cle
    wph
    cc0
    @39
    cle
    wbr
    cc0
    @39
    @26
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cle
    wbr
    wph
    cc0
    cA
    cT
    cB
    cW
    cvsca
    cfv
    #
    co
    #
    c.mi
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    @41
    cle
    wph
    cc0
    @49
    cle
    wbr
    @48
    @46
    cle
    wbr
    #
    wph
    @47
    @45
    cle
    wbr
    #
    @50
    wph
    @43
    cU
    wcel
    #
    @47
    cA
    vx
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vx
    cU
    wral
    @51
    wph
    cW
    clmod
    wcel
    #
    @6
    cT
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    cB
    cU
    wcel
    @52
    wph
    @1
    @57
    @5
    cW
    cphlmod
    syl
    #
    pjthlem.2
    wph
    cT
    @0
    @26
    cdiv
    co
    #
    @59
    pjthlem.8
    wph
    @1
    @0
    @59
    wcel
    #
    @26
    @59
    wcel
    @26
    cc0
    wne
    @62
    @59
    wcel
    @5
    wph
    cW
    cphl
    wcel
    #
    @2
    @3
    @63
    wph
    @4
    @64
    pjthlem.1
    cW
    hlphl
    syl
    pjthlem.4
    @7
    cA
    cB
    @58
    c.xi
    @59
    cV
    cW
    @58
    eqid
    #
    pjthlem.h
    pjthlem.v
    @59
    eqid
    #
    ipcl
    syl3anc
    wph
    cr
    @59
    @26
    wph
    @4
    cr
    @59
    wss
    pjthlem.1
    @58
    @59
    cW
    @65
    @66
    hlress
    syl
    @28
    sseldd
    wph
    @26
    wph
    @18
    @24
    @29
    ge0p1rpd
    #
    rpne0d
    #
    @0
    @26
    @58
    @59
    cW
    @65
    @66
    cphdivcl
    syl13anc
    syl5eqel
    #
    pjthlem.5
    @59
    cL
    @42
    cU
    @58
    cW
    cT
    cB
    @65
    @42
    eqid
    #
    @66
    pjthlem.l
    lssvscl
    syl22anc
    pjthlem.7
    @56
    @51
    vx
    @43
    cU
    @53
    @43
    wceq
    #
    @55
    @45
    @47
    cle
    @71
    @54
    @44
    cN
    @53
    @43
    cA
    c.mi
    oveq2
    fveq2d
    breq2d
    rspcv
    sylc
    wph
    @47
    @45
    wph
    cW
    cngp
    wcel
    #
    @2
    @47
    cr
    wcel
    wph
    @1
    @72
    @5
    cW
    cphngp
    syl
    #
    pjthlem.4
    cA
    cW
    cN
    cV
    pjthlem.v
    pjthlem.n
    nmcl
    syl2anc
    #
    wph
    @72
    @44
    cV
    wcel
    #
    @45
    cr
    wcel
    @73
    wph
    @57
    @2
    @43
    cV
    wcel
    #
    @75
    @61
    pjthlem.4
    wph
    @57
    @60
    @3
    @76
    @61
    @69
    @7
    cT
    @42
    @58
    @59
    cV
    cW
    cB
    pjthlem.v
    @65
    @70
    @66
    lmodvscl
    syl3anc
    #
    c.mi
    cV
    cW
    cA
    @43
    pjthlem.v
    pjthlem.m
    lmodvsubcl
    syl3anc
    #
    @44
    cW
    cN
    cV
    pjthlem.v
    pjthlem.n
    nmcl
    syl2anc
    #
    wph
    @72
    @2
    cc0
    @47
    cle
    wbr
    @73
    pjthlem.4
    cA
    cW
    cN
    cV
    pjthlem.v
    pjthlem.n
    nmge0
    syl2anc
    wph
    @72
    @75
    cc0
    @45
    cle
    wbr
    @73
    @78
    @44
    cW
    cN
    cV
    pjthlem.v
    pjthlem.n
    nmge0
    syl2anc
    le2sqd
    mpbid
    wph
    @46
    @48
    wph
    @45
    @79
    resqcld
    wph
    @47
    @74
    resqcld
    subge0d
    mpbird
    wph
    @12
    @40
    cdiv
    co
    #
    @19
    cmul
    co
    #
    cneg
    #
    cA
    cA
    c.xi
    co
    #
    caddc
    co
    #
    @83
    cmin
    co
    @82
    @49
    @41
    wph
    @82
    @83
    wph
    @81
    wph
    @81
    wph
    @80
    @19
    wph
    @12
    @40
    @22
    wph
    @26
    crp
    wcel
    c2
    cz
    wcel
    @40
    crp
    wcel
    @67
    2z
    @26
    c2
    rpexpcl
    sylancl
    #
    rerpdivcld
    #
    @25
    remulcld
    recnd
    #
    negcld
    #
    wph
    @1
    @2
    @2
    @83
    cc
    wcel
    @5
    pjthlem.4
    pjthlem.4
    cA
    cA
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    cphipcl
    syl3anc
    #
    pncand
    wph
    @46
    @84
    @48
    @83
    cmin
    wph
    @46
    @83
    @81
    cmin
    co
    #
    @83
    @82
    caddc
    co
    @84
    wph
    @46
    @44
    @44
    c.xi
    co
    #
    cA
    @44
    c.xi
    co
    #
    @43
    @44
    c.xi
    co
    #
    cmin
    co
    #
    @90
    wph
    @1
    @75
    @46
    @91
    wceq
    @5
    @78
    @44
    c.xi
    cN
    cV
    cW
    pjthlem.v
    pjthlem.h
    pjthlem.n
    nmsq
    syl2anc
    wph
    @1
    @2
    @76
    @75
    @91
    @94
    wceq
    @5
    pjthlem.4
    @77
    @78
    cA
    @43
    @44
    c.xi
    c.mi
    cV
    cW
    pjthlem.h
    pjthlem.v
    pjthlem.m
    cphsubdir
    syl13anc
    wph
    @94
    @83
    cA
    @43
    c.xi
    co
    #
    cmin
    co
    #
    @93
    cmin
    co
    @83
    @95
    @93
    caddc
    co
    #
    cmin
    co
    @90
    wph
    @92
    @96
    @93
    cmin
    wph
    @1
    @2
    @2
    @76
    @92
    @96
    wceq
    @5
    pjthlem.4
    pjthlem.4
    @77
    cA
    cA
    @43
    c.xi
    c.mi
    cV
    cW
    pjthlem.h
    pjthlem.v
    pjthlem.m
    cphsubdi
    syl13anc
    oveq1d
    wph
    @83
    @95
    @93
    @89
    wph
    @1
    @2
    @76
    @95
    cc
    wcel
    @5
    pjthlem.4
    @77
    cA
    @43
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    cphipcl
    syl3anc
    wph
    @93
    @43
    cA
    c.xi
    co
    #
    @43
    @43
    c.xi
    co
    #
    cmin
    co
    #
    cc
    wph
    @1
    @76
    @2
    @76
    @93
    @100
    wceq
    @5
    @77
    pjthlem.4
    @77
    @43
    cA
    @43
    c.xi
    c.mi
    cV
    cW
    pjthlem.h
    pjthlem.v
    pjthlem.m
    cphsubdi
    syl13anc
    #
    wph
    @98
    @99
    wph
    @1
    @76
    @2
    @98
    cc
    wcel
    @5
    @77
    pjthlem.4
    @43
    cA
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    cphipcl
    syl3anc
    wph
    @1
    @76
    @76
    @99
    cc
    wcel
    @5
    @77
    @77
    @43
    @43
    c.xi
    cV
    cW
    pjthlem.v
    pjthlem.h
    cphipcl
    syl3anc
    subcld
    eqeltrd
    subsub4d
    wph
    @97
    @81
    @83
    cmin
    wph
    @80
    @30
    cmul
    co
    @80
    @26
    cmul
    co
    #
    @80
    c1
    cmul
    co
    #
    caddc
    co
    @81
    @97
    wph
    @80
    @26
    c1
    wph
    @80
    @86
    recnd
    #
    wph
    @26
    @28
    recnd
    #
    wph
    1cnd
    adddid
    wph
    @19
    @30
    @80
    cmul
    @37
    oveq2d
    wph
    @95
    @102
    @93
    @103
    caddc
    wph
    @95
    @12
    @26
    cdiv
    co
    #
    @12
    @26
    cmul
    co
    #
    @40
    cdiv
    co
    #
    @102
    wph
    @95
    cT
    ccj
    cfv
    #
    @0
    cmul
    co
    #
    @0
    @109
    cmul
    co
    #
    @106
    wph
    @1
    @60
    @2
    @3
    @95
    @110
    wceq
    @5
    @69
    pjthlem.4
    @7
    cT
    cA
    cB
    @42
    @58
    c.xi
    @59
    cV
    cW
    pjthlem.h
    pjthlem.v
    @65
    @66
    @70
    cphassr
    syl13anc
    wph
    @109
    @0
    wph
    cT
    wph
    cT
    @62
    cc
    pjthlem.8
    wph
    @0
    @26
    @8
    @105
    @68
    divcld
    syl5eqel
    #
    cjcld
    @8
    mulcomd
    wph
    @0
    @0
    ccj
    cfv
    #
    cmul
    co
    #
    @26
    cdiv
    co
    @0
    @113
    @26
    cdiv
    co
    #
    cmul
    co
    @106
    @111
    wph
    @0
    @113
    @26
    @8
    wph
    @0
    @8
    cjcld
    @105
    @68
    divassd
    wph
    @12
    @114
    @26
    cdiv
    wph
    @0
    @8
    absvalsqd
    oveq1d
    wph
    @109
    @115
    @0
    cmul
    wph
    @109
    @62
    ccj
    cfv
    #
    @115
    cT
    @62
    ccj
    pjthlem.8
    fveq2i
    wph
    @116
    @113
    @26
    ccj
    cfv
    #
    cdiv
    co
    @115
    wph
    @0
    @26
    @8
    @105
    @68
    cjdivd
    wph
    @117
    @26
    @113
    cdiv
    wph
    @26
    @28
    cjred
    oveq2d
    eqtrd
    syl5eq
    oveq2d
    3eqtr4rd
    3eqtrd
    wph
    @108
    @26
    @12
    cmul
    co
    #
    @26
    @26
    cmul
    co
    #
    cdiv
    co
    @106
    wph
    @107
    @118
    @40
    @119
    cdiv
    wph
    @12
    @26
    wph
    @12
    @22
    recnd
    #
    @105
    mulcomd
    wph
    @26
    @105
    sqvald
    oveq12d
    wph
    @12
    @26
    @26
    @120
    @105
    @105
    @68
    @68
    divcan5d
    eqtr2d
    wph
    @12
    @26
    @40
    @120
    @105
    wph
    @40
    @85
    rpcnd
    #
    wph
    @40
    @85
    rpne0d
    #
    div23d
    3eqtrd
    #
    wph
    @100
    @102
    @80
    @18
    cmul
    co
    #
    cmin
    co
    #
    @93
    @103
    wph
    @98
    @102
    @99
    @124
    cmin
    wph
    @95
    ccj
    cfv
    #
    @95
    @98
    @102
    wph
    @95
    wph
    @95
    @102
    cr
    @123
    wph
    @80
    @26
    @86
    @28
    remulcld
    eqeltrd
    cjred
    wph
    @1
    @2
    @76
    @126
    @98
    wceq
    @5
    pjthlem.4
    @77
    cA
    @43
    c.xi
    cV
    cW
    pjthlem.h
    pjthlem.v
    cphipcj
    syl3anc
    @123
    3eqtr3d
    wph
    @99
    cT
    @109
    cmul
    co
    #
    @18
    cmul
    co
    #
    @124
    wph
    @1
    @60
    @60
    @3
    @3
    @99
    @128
    wceq
    @5
    @69
    @69
    @7
    @7
    cT
    cT
    cB
    cB
    @42
    @58
    c.xi
    @59
    cV
    cW
    pjthlem.h
    pjthlem.v
    @65
    @66
    @70
    cph2ass
    syl122anc
    wph
    @127
    @80
    @18
    cmul
    wph
    cT
    cabs
    cfv
    #
    c2
    cexp
    co
    @9
    @26
    cdiv
    co
    #
    c2
    cexp
    co
    @127
    @80
    wph
    @129
    @130
    c2
    cexp
    wph
    @129
    @62
    cabs
    cfv
    #
    @130
    cT
    @62
    cabs
    pjthlem.8
    fveq2i
    wph
    @131
    @9
    @26
    cabs
    cfv
    #
    cdiv
    co
    @130
    wph
    @0
    @26
    @8
    @105
    @68
    absdivd
    wph
    @132
    @26
    @9
    cdiv
    wph
    @26
    @28
    wph
    @26
    @67
    rpge0d
    absidd
    oveq2d
    eqtrd
    syl5eq
    oveq1d
    wph
    cT
    @112
    absvalsqd
    wph
    @9
    @26
    @11
    @105
    @68
    sqdivd
    3eqtr3d
    oveq1d
    eqtrd
    oveq12d
    @101
    wph
    @80
    @26
    @18
    cmin
    co
    #
    cmul
    co
    @103
    @125
    wph
    @133
    c1
    @80
    cmul
    wph
    @33
    @36
    @133
    c1
    wceq
    @35
    ax-1cn
    @18
    c1
    pncan2
    sylancl
    oveq2d
    wph
    @80
    @26
    @18
    @104
    @105
    @35
    subdid
    eqtr3d
    3eqtr4d
    oveq12d
    3eqtr4rd
    oveq2d
    3eqtrd
    3eqtrd
    wph
    @83
    @81
    @89
    @87
    negsubd
    wph
    @83
    @82
    @89
    @88
    addcomd
    3eqtr2d
    wph
    @1
    @2
    @48
    @83
    wceq
    @5
    pjthlem.4
    cA
    c.xi
    cN
    cV
    cW
    pjthlem.v
    pjthlem.h
    pjthlem.n
    nmsq
    syl2anc
    oveq12d
    wph
    @41
    @80
    @38
    cmul
    co
    @82
    wph
    @12
    @38
    @40
    @120
    wph
    @38
    wph
    @19
    @25
    renegcld
    #
    recnd
    @121
    @122
    div23d
    wph
    @80
    @19
    @104
    wph
    @19
    @25
    recnd
    #
    mulneg2d
    eqtrd
    3eqtr4rd
    breqtrrd
    wph
    @39
    @40
    wph
    @12
    @38
    @22
    @134
    remulcld
    @85
    ge0divd
    mpbird
    wph
    @12
    cc
    wcel
    @19
    cc
    wcel
    @21
    @39
    wceq
    @120
    @135
    @12
    @19
    mulneg12
    syl2anc
    breqtrrd
    @16
    @19
    prodge02
    syl22anc
    wph
    @12
    @22
    le0neg1d
    mpbird
    wph
    @9
    @10
    sqge0d
    wph
    @12
    cr
    wcel
    cc0
    cr
    wcel
    @13
    @14
    @15
    wa
    wb
    @22
    0re
    @12
    cc0
    letri3
    sylancl
    mpbir2and
    sqeq0d
    abs00d
end
