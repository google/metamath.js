include "cmv.mm"
include "co.mm"
include "csp.mm"
include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "cheli.mm"
include "syl.mm"
include "hvsubcl.mm"
include "syl2anc.mm"
include "hicl.mm"
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
include "hiidrcl.mm"
include "2re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "c1.mm"
include "0red.mm"
include "peano2re.mm"
include "hiidge0.mm"
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
include "csm.mm"
include "cno.mm"
include "cmin.mm"
include "cva.mm"
include "cv.mm"
include "wral.mm"
include "csh.mm"
include "chshii.mm"
include "a1i.mm"
include "ge0p1rpd.mm"
include "rpne0d.mm"
include "divcld.mm"
include "syl5eqel.mm"
include "shmulcl.mm"
include "syl3anc.mm"
include "shaddcl.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "hvsubass.mm"
include "normcl.mm"
include "normge0.mm"
include "letrd.mm"
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
include "normsq.mm"
include "his2sub.mm"
include "his2sub2.mm"
include "oveq1d.mm"
include "subcld.mm"
include "eqeltrd.mm"
include "subsub4d.mm"
include "adddid.mm"
include "oveq2d.mm"
include "ccj.mm"
include "his5.mm"
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
include "div23d.mm"
include "wb.mm"
include "hire.mm"
include "eqtr3d.mm"
include "his35.mm"
include "syl22anc.mm"
include "absdivd.mm"
include "rpge0d.mm"
include "absidd.mm"
include "sqdivd.mm"
include "3eqtr3d.mm"
include "pncan2.mm"
include "subdid.mm"
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
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "sqeq0d.mm"
include "abs00d.mm"

theorem pjhthlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let cH: class H
  let vy: setvar y
  let vz: setvar z
  assume pjhth.1: |- H e. CH
  assume pjhth.2: |- ( ph -> A e. ~H )
  assume pjhth.3: |- ( ph -> B e. H )
  assume pjhth.4: |- ( ph -> C e. H )
  assume pjhth.5: |- ( ph -> A. x e. H ( normh ` ( A -h B ) ) <_ ( normh ` ( A -h x ) ) )
  assume pjhth.6: |- T = ( ( ( A -h B ) .ih C ) / ( ( C .ih C ) + 1 ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint H x
  disjoint T x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint H y
  disjoint H z
  assert |- ( ph -> ( ( A -h B ) .ih C ) = 0 )

  proof
    wph
    cA
    cB
    cmv
    co
    #
    cC
    csp
    co
    #
    wph
    @0
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    @1
    cc
    wcel
    wph
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    @2
    pjhth.2
    wph
    cB
    cH
    wcel
    #
    @5
    pjhth.3
    cB
    cH
    pjhth.1
    cheli
    syl
    #
    cA
    cB
    hvsubcl
    syl2anc
    #
    wph
    cC
    cH
    wcel
    #
    @3
    pjhth.4
    cC
    cH
    pjhth.1
    cheli
    syl
    #
    @0
    cC
    hicl
    syl2anc
    #
    wph
    @1
    cabs
    cfv
    #
    wph
    @12
    wph
    @1
    @11
    abscld
    #
    recnd
    #
    wph
    @12
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @15
    cc0
    cle
    wbr
    #
    cc0
    @15
    cle
    wbr
    #
    wph
    @17
    cc0
    @15
    cneg
    #
    cle
    wbr
    #
    wph
    @19
    cr
    wcel
    cC
    cC
    csp
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
    @22
    clt
    wbr
    cc0
    @19
    @22
    cmul
    co
    #
    cle
    wbr
    @20
    wph
    @15
    wph
    @12
    @13
    resqcld
    #
    renegcld
    wph
    @21
    cr
    wcel
    #
    c2
    cr
    wcel
    @23
    wph
    @3
    @26
    @10
    cC
    hiidrcl
    syl
    #
    2re
    @21
    c2
    readdcl
    sylancl
    #
    wph
    cc0
    @21
    c1
    caddc
    co
    #
    @22
    wph
    0red
    #
    wph
    @26
    @29
    cr
    wcel
    @27
    @21
    peano2re
    syl
    #
    @28
    wph
    cc0
    @21
    @29
    @30
    @27
    @31
    wph
    @3
    cc0
    @21
    cle
    wbr
    @10
    cC
    hiidge0
    syl
    #
    wph
    @21
    @27
    ltp1d
    lelttrd
    wph
    @29
    @29
    c1
    caddc
    co
    #
    @22
    clt
    wph
    @29
    @31
    ltp1d
    wph
    @33
    @21
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @22
    wph
    @21
    cc
    wcel
    #
    @33
    @35
    wceq
    #
    wph
    @21
    @27
    recnd
    #
    @36
    c1
    cc
    wcel
    #
    @39
    @37
    ax-1cn
    ax-1cn
    @21
    c1
    c1
    addass
    mp3an23
    syl
    c2
    @34
    @21
    caddc
    df-2
    oveq2i
    syl6reqr
    #
    breqtrrd
    lttrd
    wph
    cc0
    @15
    @22
    cneg
    #
    cmul
    co
    #
    @24
    cle
    wph
    cc0
    @42
    cle
    wbr
    cc0
    @42
    @29
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
    @0
    cT
    cC
    csm
    co
    #
    cmv
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @0
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    @44
    cle
    wph
    cc0
    @51
    cle
    wbr
    @50
    @48
    cle
    wbr
    #
    wph
    @49
    @47
    cle
    wbr
    @52
    wph
    @49
    cA
    cB
    @45
    cva
    co
    #
    cmv
    co
    #
    cno
    cfv
    #
    @47
    cle
    wph
    @53
    cH
    wcel
    #
    @49
    cA
    vx
    cv
    #
    cmv
    co
    #
    cno
    cfv
    #
    cle
    wbr
    #
    vx
    cH
    wral
    @49
    @55
    cle
    wbr
    #
    wph
    cH
    csh
    wcel
    #
    @6
    @45
    cH
    wcel
    #
    @56
    @62
    wph
    cH
    pjhth.1
    chshii
    a1i
    #
    pjhth.3
    wph
    @62
    cT
    cc
    wcel
    #
    @9
    @63
    @64
    wph
    cT
    @1
    @29
    cdiv
    co
    #
    cc
    pjhth.6
    wph
    @1
    @29
    @11
    wph
    @29
    @31
    recnd
    #
    wph
    @29
    wph
    @21
    @27
    @32
    ge0p1rpd
    #
    rpne0d
    #
    divcld
    syl5eqel
    #
    pjhth.4
    cT
    cC
    cH
    shmulcl
    syl3anc
    #
    cB
    @45
    cH
    shaddcl
    syl3anc
    pjhth.5
    @60
    @61
    vx
    @53
    cH
    @57
    @53
    wceq
    #
    @59
    @55
    @49
    cle
    @72
    @58
    @54
    cno
    @57
    @53
    cA
    cmv
    oveq2
    fveq2d
    breq2d
    rspcv
    sylc
    wph
    @46
    @54
    cno
    wph
    @4
    @5
    @45
    chil
    wcel
    #
    @46
    @54
    wceq
    pjhth.2
    @7
    wph
    @63
    @73
    @71
    @45
    cH
    pjhth.1
    cheli
    syl
    #
    cA
    cB
    @45
    hvsubass
    syl3anc
    fveq2d
    breqtrrd
    #
    wph
    @49
    @47
    wph
    @2
    @49
    cr
    wcel
    @8
    @0
    normcl
    syl
    #
    wph
    @46
    chil
    wcel
    #
    @47
    cr
    wcel
    wph
    @2
    @73
    @77
    @8
    @74
    @0
    @45
    hvsubcl
    syl2anc
    #
    @46
    normcl
    syl
    #
    wph
    @2
    cc0
    @49
    cle
    wbr
    @8
    @0
    normge0
    syl
    #
    wph
    cc0
    @49
    @47
    @30
    @76
    @79
    @80
    @75
    letrd
    le2sqd
    mpbid
    wph
    @48
    @50
    wph
    @47
    @79
    resqcld
    wph
    @49
    @76
    resqcld
    subge0d
    mpbird
    wph
    @15
    @43
    cdiv
    co
    #
    @22
    cmul
    co
    #
    cneg
    #
    @0
    @0
    csp
    co
    #
    caddc
    co
    #
    @84
    cmin
    co
    @83
    @51
    @44
    wph
    @83
    @84
    wph
    @82
    wph
    @82
    wph
    @81
    @22
    wph
    @15
    @43
    @25
    wph
    @29
    crp
    wcel
    c2
    cz
    wcel
    @43
    crp
    wcel
    @68
    2z
    @29
    c2
    rpexpcl
    sylancl
    #
    rerpdivcld
    #
    @28
    remulcld
    recnd
    #
    negcld
    #
    wph
    @2
    @2
    @84
    cc
    wcel
    @8
    @8
    @0
    @0
    hicl
    syl2anc
    #
    pncand
    wph
    @48
    @85
    @50
    @84
    cmin
    wph
    @48
    @84
    @82
    cmin
    co
    #
    @84
    @83
    caddc
    co
    @85
    wph
    @48
    @46
    @46
    csp
    co
    #
    @0
    @46
    csp
    co
    #
    @45
    @46
    csp
    co
    #
    cmin
    co
    #
    @91
    wph
    @77
    @48
    @92
    wceq
    @78
    @46
    normsq
    syl
    wph
    @2
    @73
    @77
    @92
    @95
    wceq
    @8
    @74
    @78
    @0
    @45
    @46
    his2sub
    syl3anc
    wph
    @95
    @84
    @0
    @45
    csp
    co
    #
    cmin
    co
    #
    @94
    cmin
    co
    @84
    @96
    @94
    caddc
    co
    #
    cmin
    co
    @91
    wph
    @93
    @97
    @94
    cmin
    wph
    @2
    @2
    @73
    @93
    @97
    wceq
    @8
    @8
    @74
    @0
    @0
    @45
    his2sub2
    syl3anc
    oveq1d
    wph
    @84
    @96
    @94
    @90
    wph
    @2
    @73
    @96
    cc
    wcel
    @8
    @74
    @0
    @45
    hicl
    syl2anc
    wph
    @94
    @45
    @0
    csp
    co
    #
    @45
    @45
    csp
    co
    #
    cmin
    co
    #
    cc
    wph
    @73
    @2
    @73
    @94
    @101
    wceq
    @74
    @8
    @74
    @45
    @0
    @45
    his2sub2
    syl3anc
    #
    wph
    @99
    @100
    wph
    @73
    @2
    @99
    cc
    wcel
    @74
    @8
    @45
    @0
    hicl
    syl2anc
    wph
    @73
    @73
    @100
    cc
    wcel
    @74
    @74
    @45
    @45
    hicl
    syl2anc
    subcld
    eqeltrd
    subsub4d
    wph
    @98
    @82
    @84
    cmin
    wph
    @81
    @33
    cmul
    co
    @81
    @29
    cmul
    co
    #
    @81
    c1
    cmul
    co
    #
    caddc
    co
    @82
    @98
    wph
    @81
    @29
    c1
    wph
    @81
    @87
    recnd
    #
    @67
    @39
    wph
    ax-1cn
    a1i
    adddid
    wph
    @22
    @33
    @81
    cmul
    @40
    oveq2d
    wph
    @96
    @103
    @94
    @104
    caddc
    wph
    @96
    @15
    @29
    cdiv
    co
    #
    @15
    @29
    cmul
    co
    #
    @43
    cdiv
    co
    #
    @103
    wph
    @96
    cT
    ccj
    cfv
    #
    @1
    cmul
    co
    #
    @1
    @109
    cmul
    co
    #
    @106
    wph
    @65
    @2
    @3
    @96
    @110
    wceq
    @70
    @8
    @10
    cT
    @0
    cC
    his5
    syl3anc
    wph
    @109
    @1
    wph
    cT
    @70
    cjcld
    @11
    mulcomd
    wph
    @1
    @1
    ccj
    cfv
    #
    cmul
    co
    #
    @29
    cdiv
    co
    @1
    @112
    @29
    cdiv
    co
    #
    cmul
    co
    @106
    @111
    wph
    @1
    @112
    @29
    @11
    wph
    @1
    @11
    cjcld
    @67
    @69
    divassd
    wph
    @15
    @113
    @29
    cdiv
    wph
    @1
    @11
    absvalsqd
    oveq1d
    wph
    @109
    @114
    @1
    cmul
    wph
    @109
    @66
    ccj
    cfv
    #
    @114
    cT
    @66
    ccj
    pjhth.6
    fveq2i
    wph
    @115
    @112
    @29
    ccj
    cfv
    #
    cdiv
    co
    @114
    wph
    @1
    @29
    @11
    @67
    @69
    cjdivd
    wph
    @116
    @29
    @112
    cdiv
    wph
    @29
    @31
    cjred
    oveq2d
    eqtrd
    syl5eq
    oveq2d
    3eqtr4rd
    3eqtrd
    wph
    @108
    @29
    @15
    cmul
    co
    #
    @29
    @29
    cmul
    co
    #
    cdiv
    co
    @106
    wph
    @107
    @117
    @43
    @118
    cdiv
    wph
    @15
    @29
    wph
    @15
    @25
    recnd
    #
    @67
    mulcomd
    wph
    @29
    @67
    sqvald
    oveq12d
    wph
    @15
    @29
    @29
    @119
    @67
    @67
    @69
    @69
    divcan5d
    eqtr2d
    wph
    @15
    @29
    @43
    @119
    @67
    wph
    @43
    wph
    @29
    @31
    resqcld
    recnd
    #
    wph
    @43
    @86
    rpne0d
    #
    div23d
    3eqtrd
    #
    wph
    @101
    @103
    @81
    @21
    cmul
    co
    #
    cmin
    co
    #
    @94
    @104
    wph
    @99
    @103
    @100
    @123
    cmin
    wph
    @96
    @99
    @103
    wph
    @96
    cr
    wcel
    #
    @96
    @99
    wceq
    #
    wph
    @96
    @103
    cr
    @122
    wph
    @81
    @29
    @87
    @31
    remulcld
    eqeltrd
    wph
    @2
    @73
    @125
    @126
    wb
    @8
    @74
    @0
    @45
    hire
    syl2anc
    mpbid
    @122
    eqtr3d
    wph
    @100
    cT
    @109
    cmul
    co
    #
    @21
    cmul
    co
    #
    @123
    wph
    @65
    @65
    @3
    @3
    @100
    @128
    wceq
    @70
    @70
    @10
    @10
    cT
    cT
    cC
    cC
    his35
    syl22anc
    wph
    @127
    @81
    @21
    cmul
    wph
    cT
    cabs
    cfv
    #
    c2
    cexp
    co
    @12
    @29
    cdiv
    co
    #
    c2
    cexp
    co
    @127
    @81
    wph
    @129
    @130
    c2
    cexp
    wph
    @129
    @66
    cabs
    cfv
    #
    @130
    cT
    @66
    cabs
    pjhth.6
    fveq2i
    wph
    @131
    @12
    @29
    cabs
    cfv
    #
    cdiv
    co
    @130
    wph
    @1
    @29
    @11
    @67
    @69
    absdivd
    wph
    @132
    @29
    @12
    cdiv
    wph
    @29
    @31
    wph
    @29
    @68
    rpge0d
    absidd
    oveq2d
    eqtrd
    syl5eq
    oveq1d
    wph
    cT
    @70
    absvalsqd
    wph
    @12
    @29
    @14
    @67
    @69
    sqdivd
    3eqtr3d
    oveq1d
    eqtrd
    oveq12d
    @102
    wph
    @81
    @29
    @21
    cmin
    co
    #
    cmul
    co
    @104
    @124
    wph
    @133
    c1
    @81
    cmul
    wph
    @36
    @39
    @133
    c1
    wceq
    @38
    ax-1cn
    @21
    c1
    pncan2
    sylancl
    oveq2d
    wph
    @81
    @29
    @21
    @105
    @67
    @38
    subdid
    eqtr3d
    3eqtr4d
    oveq12d
    3eqtr4rd
    oveq2d
    3eqtrd
    3eqtrd
    wph
    @84
    @82
    @90
    @88
    negsubd
    wph
    @84
    @83
    @90
    @89
    addcomd
    3eqtr2d
    wph
    @2
    @50
    @84
    wceq
    @8
    @0
    normsq
    syl
    oveq12d
    wph
    @44
    @81
    @41
    cmul
    co
    @83
    wph
    @15
    @41
    @43
    @119
    wph
    @41
    wph
    @22
    @28
    renegcld
    #
    recnd
    @120
    @121
    div23d
    wph
    @81
    @22
    @105
    wph
    @22
    @28
    recnd
    #
    mulneg2d
    eqtrd
    3eqtr4rd
    breqtrrd
    wph
    @42
    @43
    wph
    @15
    @41
    @25
    @134
    remulcld
    @86
    ge0divd
    mpbird
    wph
    @15
    cc
    wcel
    @22
    cc
    wcel
    @24
    @42
    wceq
    @119
    @135
    @15
    @22
    mulneg12
    syl2anc
    breqtrrd
    @19
    @22
    prodge02
    syl22anc
    wph
    @15
    @25
    le0neg1d
    mpbird
    wph
    @12
    @13
    sqge0d
    wph
    @15
    cr
    wcel
    cc0
    cr
    wcel
    @16
    @17
    @18
    wa
    wb
    @25
    0re
    @15
    cc0
    letri3
    sylancl
    mpbir2and
    sqeq0d
    abs00d
end
