include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cabs.mm"
include "c2.mm"
include "cmul.mm"
include "cexp.mm"
include "cdiv.mm"
include "cneg.mm"
include "caddc.mm"
include "cr.mm"
include "wceq.mm"
include "a1i.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "knoppndvlem1.mm"
include "eqeltrd.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "knoppndvlem5.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "fzfid.mm"
include "wa.mm"
include "2re.mm"
include "cn.mm"
include "nnre.mm"
include "syl.mm"
include "remulcld.mm"
include "adantr.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "reexpcld.mm"
include "fsumrecl.mm"
include "wne.mm"
include "2ne0.mm"
include "redivcld.mm"
include "1red.mm"
include "0red.mm"
include "0lt1.mm"
include "knoppndvlem12.mm"
include "simprd.mm"
include "lttrd.mm"
include "jca.mm"
include "ltne.mm"
include "knoppndvlem11.mm"
include "cle.mm"
include "oveq12d.mm"
include "nnge1.mm"
include "ltletrd.mm"
include "mulne0d.mm"
include "znegcld.mm"
include "reexpclzd.mm"
include "zcnd.mm"
include "subdid.mm"
include "eqcomd.mm"
include "1cnd.mm"
include "pncan2d.mm"
include "oveq2d.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "cc.mm"
include "cz.mm"
include "w3a.mm"
include "mulcld.mm"
include "3jca.mm"
include "absexpz.mm"
include "absmuld.mm"
include "0le2.mm"
include "pm3.2i.mm"
include "absid.mm"
include "ax-mp.mm"
include "ltled.mm"
include "absidd.mm"
include "oveq1d.mm"
include "geoser.mm"
include "expcld.mm"
include "necomd.mm"
include "div2subd.mm"
include "eqeltrrd.mm"
include "crp.mm"
include "2rp.mm"
include "rpgt0d.mm"
include "mulgt0d.mm"
include "expgt0.mm"
include "divge0d.mm"
include "elrpd.mm"
include "lem1d.mm"
include "lediv1dd.mm"
include "lemul2ad.mm"
include "divrecd.mm"
include "mulassd.mm"
include "div23d.mm"
include "knoppndvlem13.mm"
include "absne0d.mm"
include "mulexpz.mm"
include "jca32.mm"
include "expaddz.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "negidd.mm"
include "exp0d.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "letrd.mm"

theorem knoppndvlem14
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  assume knoppndvlem14.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem14.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem14.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem14.b: |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) )
  assume knoppndvlem14.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem14.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem14.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem14.n: |- ( ph -> N e. NN )
  assume knoppndvlem14.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )

  disjoint A i
  disjoint A n
  disjoint A y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint A x
  disjoint i x
  disjoint B i
  disjoint B n
  disjoint B y
  disjoint B x
  disjoint C i
  disjoint C n
  disjoint C y
  disjoint J i
  disjoint J n
  disjoint J y
  disjoint N i
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint n ph
  disjoint ph y
  assert |- ( ph -> ( abs ` ( sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` B ) ` i ) - sum_ i e. ( 0 ... ( J - 1 ) ) ( ( F ` A ) ` i ) ) ) <_ ( ( ( ( abs ` C ) ^ J ) / 2 ) x. ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) )

  proof
    wph
    cc0
    cJ
    c1
    cmin
    co
    #
    cfz
    co
    #
    vi
    cv
    #
    cB
    cF
    cfv
    cfv
    vi
    csu
    #
    @1
    @2
    cA
    cF
    cfv
    cfv
    vi
    csu
    #
    cmin
    co
    #
    cabs
    cfv
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    c2
    cN
    cmul
    co
    #
    cC
    cabs
    cfv
    #
    cmul
    co
    #
    @2
    cexp
    co
    #
    vi
    csu
    #
    cmul
    co
    #
    @9
    cJ
    cexp
    co
    #
    c2
    cdiv
    co
    #
    c1
    @10
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    wph
    @5
    wph
    @5
    wph
    @3
    @4
    wph
    vx
    vy
    cB
    cC
    cT
    vi
    vn
    cF
    @0
    cN
    knoppndvlem14.t
    knoppndvlem14.f
    wph
    cB
    @8
    cJ
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cM
    c1
    caddc
    co
    #
    cmul
    co
    #
    cr
    cB
    @23
    wceq
    wph
    knoppndvlem14.b
    a1i
    #
    wph
    cJ
    @22
    cN
    knoppndvlem14.n
    wph
    cJ
    knoppndvlem14.j
    nn0zd
    #
    wph
    cM
    knoppndvlem14.m
    peano2zd
    #
    knoppndvlem1
    eqeltrd
    #
    wph
    cC
    cr
    wcel
    @9
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem14.c
    knoppndvlem3
    simpld
    #
    knoppndvlem14.n
    knoppndvlem5
    wph
    vx
    vy
    cA
    cC
    cT
    vi
    vn
    cF
    @0
    cN
    knoppndvlem14.t
    knoppndvlem14.f
    wph
    cA
    @21
    cM
    cmul
    co
    #
    cr
    cA
    @29
    wceq
    wph
    knoppndvlem14.a
    a1i
    #
    wph
    cJ
    cM
    cN
    knoppndvlem14.n
    @25
    knoppndvlem14.m
    knoppndvlem1
    eqeltrd
    #
    @28
    knoppndvlem14.n
    knoppndvlem5
    resubcld
    recnd
    abscld
    wph
    @7
    @12
    wph
    @6
    wph
    @6
    wph
    cB
    cA
    @27
    @31
    resubcld
    recnd
    abscld
    wph
    @1
    @11
    vi
    wph
    cc0
    @0
    fzfid
    wph
    @2
    @1
    wcel
    #
    wa
    @10
    @2
    wph
    @10
    cr
    wcel
    @32
    wph
    @8
    @9
    wph
    c2
    cN
    c2
    cr
    wcel
    #
    wph
    2re
    a1i
    #
    wph
    cN
    cn
    wcel
    #
    cN
    cr
    wcel
    knoppndvlem14.n
    cN
    nnre
    syl
    #
    remulcld
    #
    wph
    cC
    wph
    cC
    @28
    recnd
    #
    abscld
    #
    remulcld
    #
    adantr
    @32
    @2
    cn0
    wcel
    wph
    @2
    @0
    elfznn0
    adantl
    reexpcld
    fsumrecl
    #
    remulcld
    wph
    @15
    @17
    wph
    @14
    c2
    wph
    @9
    cJ
    @39
    knoppndvlem14.j
    reexpcld
    #
    @34
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    redivcld
    wph
    c1
    @16
    wph
    1red
    #
    wph
    @10
    c1
    @40
    @44
    resubcld
    #
    wph
    cc0
    cr
    wcel
    #
    cc0
    @16
    clt
    wbr
    #
    wa
    @16
    cc0
    wne
    wph
    @46
    @47
    wph
    0red
    #
    wph
    cc0
    c1
    @16
    @48
    @44
    @45
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    #
    wph
    @10
    c1
    wne
    #
    c1
    @16
    clt
    wbr
    #
    wph
    cC
    cN
    knoppndvlem14.c
    knoppndvlem14.n
    knoppndvlem14.1
    knoppndvlem12
    #
    simprd
    lttrd
    #
    jca
    cc0
    @16
    ltne
    syl
    #
    redivcld
    #
    remulcld
    wph
    vx
    vy
    cA
    cB
    cC
    cT
    vi
    vn
    cF
    cJ
    cN
    knoppndvlem14.t
    knoppndvlem14.f
    @31
    @27
    knoppndvlem14.c
    knoppndvlem14.j
    knoppndvlem14.n
    knoppndvlem11
    wph
    @13
    @21
    @10
    cJ
    cexp
    co
    #
    c1
    cmin
    co
    #
    @16
    cdiv
    co
    #
    cmul
    co
    #
    @18
    cle
    wph
    @7
    @21
    @12
    @58
    cmul
    wph
    @7
    @21
    cabs
    cfv
    #
    @21
    wph
    @6
    @21
    cabs
    wph
    @6
    @23
    @29
    cmin
    co
    #
    @21
    wph
    cB
    @23
    cA
    @29
    cmin
    @24
    @30
    oveq12d
    wph
    @61
    @21
    @22
    cM
    cmin
    co
    #
    cmul
    co
    #
    @21
    c1
    cmul
    co
    @21
    wph
    @63
    @61
    wph
    @21
    @22
    cM
    wph
    @21
    wph
    @20
    c2
    wph
    @8
    @19
    @37
    wph
    c2
    cN
    wph
    c2
    @34
    recnd
    #
    wph
    cN
    @36
    recnd
    #
    @43
    wph
    @46
    cc0
    cN
    clt
    wbr
    #
    wa
    cN
    cc0
    wne
    wph
    @46
    @66
    @48
    wph
    cc0
    c1
    cN
    @48
    @44
    @36
    @49
    wph
    @35
    c1
    cN
    cle
    wbr
    knoppndvlem14.n
    cN
    nnge1
    syl
    ltletrd
    #
    jca
    cc0
    cN
    ltne
    syl
    mulne0d
    #
    wph
    cJ
    @25
    znegcld
    #
    reexpclzd
    #
    @34
    @43
    redivcld
    #
    recnd
    #
    wph
    @22
    @26
    zcnd
    wph
    cM
    knoppndvlem14.m
    zcnd
    #
    subdid
    eqcomd
    wph
    @62
    c1
    @21
    cmul
    wph
    cM
    c1
    @73
    wph
    1cnd
    #
    pncan2d
    oveq2d
    wph
    @21
    @72
    mulid1d
    3eqtrd
    eqtrd
    fveq2d
    wph
    @60
    @20
    cabs
    cfv
    #
    c2
    cabs
    cfv
    #
    cdiv
    co
    @21
    wph
    @20
    c2
    wph
    @20
    @70
    recnd
    #
    @64
    @43
    absdivd
    wph
    @75
    @20
    @76
    c2
    cdiv
    wph
    @75
    @8
    cabs
    cfv
    #
    @19
    cexp
    co
    #
    @20
    wph
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    @19
    cz
    wcel
    #
    w3a
    @75
    @79
    wceq
    wph
    @80
    @81
    @82
    wph
    c2
    cN
    @64
    @65
    mulcld
    #
    @68
    @69
    3jca
    @8
    @19
    absexpz
    syl
    wph
    @78
    @8
    @19
    cexp
    wph
    @78
    @76
    cN
    cabs
    cfv
    #
    cmul
    co
    @8
    wph
    c2
    cN
    @64
    @65
    absmuld
    wph
    @76
    c2
    @84
    cN
    cmul
    @76
    c2
    wceq
    #
    wph
    @33
    cc0
    c2
    cle
    wbr
    #
    wa
    @85
    @33
    @86
    2re
    0le2
    pm3.2i
    c2
    absid
    ax-mp
    a1i
    #
    wph
    cN
    @36
    wph
    cc0
    cN
    @48
    @36
    @67
    ltled
    absidd
    oveq12d
    eqtrd
    oveq1d
    eqtrd
    @87
    oveq12d
    eqtrd
    eqtrd
    wph
    @12
    c1
    @56
    cmin
    co
    c1
    @10
    cmin
    co
    cdiv
    co
    @58
    wph
    @10
    vi
    cJ
    wph
    @10
    @40
    recnd
    #
    wph
    @50
    @51
    @52
    simpld
    #
    knoppndvlem14.j
    geoser
    wph
    c1
    @56
    c1
    @10
    @74
    wph
    @10
    cJ
    @88
    knoppndvlem14.j
    expcld
    #
    @74
    @88
    wph
    @10
    c1
    @89
    necomd
    div2subd
    eqtrd
    #
    oveq12d
    wph
    @59
    @21
    @56
    @16
    cdiv
    co
    #
    cmul
    co
    #
    @18
    cle
    wph
    @58
    @92
    @21
    wph
    @12
    @58
    cr
    @91
    @41
    eqeltrrd
    wph
    @56
    @16
    wph
    @10
    cJ
    @40
    knoppndvlem14.j
    reexpcld
    #
    @45
    @54
    redivcld
    @71
    wph
    @20
    c2
    @70
    c2
    crp
    wcel
    wph
    2rp
    a1i
    #
    wph
    cc0
    @20
    @48
    @70
    wph
    @8
    cr
    wcel
    #
    @82
    cc0
    @8
    clt
    wbr
    #
    w3a
    cc0
    @20
    clt
    wbr
    wph
    @96
    @82
    @97
    @37
    @69
    wph
    c2
    cN
    @34
    @36
    wph
    c2
    @95
    rpgt0d
    @67
    mulgt0d
    3jca
    @8
    @19
    expgt0
    syl
    ltled
    divge0d
    wph
    @57
    @56
    @16
    wph
    @56
    c1
    @94
    @44
    resubcld
    @94
    wph
    @16
    @45
    @53
    elrpd
    wph
    @56
    @94
    lem1d
    lediv1dd
    lemul2ad
    wph
    @93
    @21
    @56
    @17
    cmul
    co
    #
    cmul
    co
    #
    @21
    @56
    cmul
    co
    #
    @17
    cmul
    co
    #
    @18
    wph
    @92
    @98
    @21
    cmul
    wph
    @56
    @16
    @90
    wph
    @16
    @45
    recnd
    @54
    divrecd
    oveq2d
    wph
    @101
    @99
    wph
    @21
    @56
    @17
    @72
    @90
    wph
    @17
    @55
    recnd
    mulassd
    eqcomd
    wph
    @100
    @15
    @17
    cmul
    wph
    @100
    @20
    @56
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @15
    wph
    @103
    @100
    wph
    @20
    @56
    c2
    @77
    @90
    @64
    @43
    div23d
    eqcomd
    wph
    @102
    @14
    c2
    cdiv
    wph
    @102
    @20
    @8
    cJ
    cexp
    co
    #
    @14
    cmul
    co
    #
    cmul
    co
    #
    @20
    @104
    cmul
    co
    #
    @14
    cmul
    co
    #
    @14
    wph
    @56
    @105
    @20
    cmul
    wph
    @80
    @81
    wa
    #
    @9
    cc
    wcel
    #
    @9
    cc0
    wne
    #
    wa
    #
    cJ
    cz
    wcel
    #
    w3a
    @56
    @105
    wceq
    wph
    @109
    @112
    @113
    wph
    @80
    @81
    @83
    @68
    jca
    #
    wph
    @110
    @111
    wph
    @9
    @39
    recnd
    wph
    cC
    @38
    wph
    cC
    cN
    knoppndvlem14.c
    knoppndvlem14.n
    knoppndvlem14.1
    knoppndvlem13
    absne0d
    jca
    @25
    3jca
    @8
    @9
    cJ
    mulexpz
    syl
    oveq2d
    wph
    @108
    @106
    wph
    @20
    @104
    @14
    @77
    wph
    @8
    cJ
    @83
    knoppndvlem14.j
    expcld
    wph
    @14
    @42
    recnd
    #
    mulassd
    eqcomd
    wph
    @108
    c1
    @14
    cmul
    co
    @14
    wph
    @107
    c1
    @14
    cmul
    wph
    @107
    @8
    @19
    cJ
    caddc
    co
    #
    cexp
    co
    #
    @8
    cc0
    cexp
    co
    c1
    wph
    @117
    @107
    wph
    @109
    @82
    @113
    wa
    wa
    @117
    @107
    wceq
    wph
    @109
    @82
    @113
    @114
    @69
    @25
    jca32
    @8
    @19
    cJ
    expaddz
    syl
    eqcomd
    wph
    @116
    cc0
    @8
    cexp
    wph
    @116
    cJ
    @19
    caddc
    co
    cc0
    wph
    @19
    cJ
    wph
    @19
    @69
    zcnd
    wph
    cJ
    knoppndvlem14.j
    nn0cnd
    #
    addcomd
    wph
    cJ
    @118
    negidd
    eqtrd
    oveq2d
    wph
    @8
    @83
    exp0d
    3eqtrd
    oveq1d
    wph
    @14
    @115
    mulid2d
    eqtrd
    3eqtrd
    oveq1d
    eqtrd
    oveq1d
    3eqtrd
    breqtrd
    eqbrtrd
    letrd
end
