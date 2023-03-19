include "citg.mm"
include "cmin.mm"
include "co.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "cneg.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "csu.mm"
include "eqid.mm"
include "dfitg.mm"
include "cn0.mm"
include "wceq.mm"
include "c2.mm"
include "nn0uz.mm"
include "df-3.mm"
include "oveq2.mm"
include "i3.mm"
include "syl6eq.mm"
include "itgvallem.mm"
include "oveq12d.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "expcl.mm"
include "sylan.mm"
include "cz.mm"
include "nn0z.mm"
include "eqidd.mm"
include "iblitg.mm"
include "recnd.mm"
include "sylan2.mm"
include "mulcld.mm"
include "c1.mm"
include "df-2.mm"
include "i2.mm"
include "1e0p1.mm"
include "exp1.mm"
include "ax-mp.mm"
include "0z.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "div1d.mm"
include "fveq2d.mm"
include "ibllem.mm"
include "mpteq2dv.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "w3a.mm"
include "iblcnlem.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simpld.mm"
include "mulid2d.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "exp0.mm"
include "fsum1.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "0nn0.mm"
include "jctil.mm"
include "cim.mm"
include "imval.mm"
include "syl5req.mm"
include "fsump1i.mm"
include "renegd.mm"
include "ax-1cn.mm"
include "negnegi.mm"
include "oveq2i.mm"
include "negcld.mm"
include "syl5eq.mm"
include "wne.mm"
include "negcli.mm"
include "neg1ne0.mm"
include "div2neg.mm"
include "mp3an23.mm"
include "simprd.mm"
include "mulm1d.mm"
include "simp3d.mm"
include "mulcl.mm"
include "addcld.mm"
include "negsubd.mm"
include "addsubd.mm"
include "3eqtrd.mm"
include "imnegd.mm"
include "eqcomi.mm"
include "ine0.mm"
include "negne0i.mm"
include "3eqtr3d.mm"
include "mulneg12.mm"
include "subcld.mm"
include "addassd.mm"
include "adddid.mm"

theorem itgcnlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let vk: setvar k
  assume itgcnlem.r: |- R = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Re ` B ) ) , ( Re ` B ) , 0 ) ) )
  assume itgcnlem.s: |- S = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u ( Re ` B ) ) , -u ( Re ` B ) , 0 ) ) )
  assume itgcnlem.t: |- T = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Im ` B ) ) , ( Im ` B ) , 0 ) ) )
  assume itgcnlem.u: |- U = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u ( Im ` B ) ) , -u ( Im ` B ) , 0 ) ) )
  assume itgcnlem.v: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgcnlem.i: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> S. A B _d x = ( ( R - S ) + ( _i x. ( T - U ) ) ) )

  proof
    wph
    vx
    cA
    cB
    citg
    #
    cR
    cS
    cmin
    co
    #
    ci
    cT
    cmul
    co
    #
    caddc
    co
    #
    ci
    cU
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    @2
    @5
    caddc
    co
    #
    caddc
    co
    @1
    ci
    cT
    cU
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    wph
    @0
    cc0
    c3
    cfz
    co
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    @11
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    wa
    @13
    cc0
    cif
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    @6
    vx
    cA
    cB
    @13
    vk
    @13
    eqid
    dfitg
    wph
    c3
    cn0
    wcel
    @17
    @6
    wceq
    wph
    @16
    ci
    cneg
    #
    vx
    cr
    @12
    cc0
    cB
    @18
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    @20
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    @3
    @6
    vk
    c2
    cc0
    c3
    cn0
    nn0uz
    df-3
    @10
    c3
    wceq
    #
    @11
    @18
    @15
    @23
    cmul
    @25
    @11
    ci
    c3
    cexp
    co
    @18
    @10
    c3
    ci
    cexp
    oveq2
    i3
    syl6eq
    vx
    cA
    cB
    @18
    vk
    c3
    i3
    itgvallem
    oveq12d
    wph
    @10
    cn0
    wcel
    #
    wa
    @11
    @15
    wph
    ci
    cc
    wcel
    #
    @26
    @11
    cc
    wcel
    @27
    wph
    ax-icn
    a1i
    #
    ci
    @10
    expcl
    sylan
    @26
    wph
    @10
    cz
    wcel
    #
    @15
    cc
    wcel
    @10
    nn0z
    wph
    @29
    wa
    @15
    wph
    vx
    cA
    cB
    @13
    @14
    @10
    cV
    wph
    @14
    eqidd
    wph
    @12
    wa
    #
    @13
    eqidd
    itgcnlem.i
    itgcnlem.v
    iblitg
    recnd
    sylan2
    mulcld
    #
    wph
    @16
    c1
    cneg
    #
    vx
    cr
    @12
    cc0
    cB
    @32
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    @34
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    cR
    @2
    caddc
    co
    #
    @3
    vk
    c1
    cc0
    c2
    cn0
    nn0uz
    df-2
    @10
    c2
    wceq
    #
    @11
    @32
    @15
    @37
    cmul
    @40
    @11
    ci
    c2
    cexp
    co
    @32
    @10
    c2
    ci
    cexp
    oveq2
    i2
    syl6eq
    vx
    cA
    cB
    @32
    vk
    c2
    i2
    itgvallem
    oveq12d
    @31
    wph
    @16
    ci
    vx
    cr
    @12
    cc0
    cB
    ci
    cdiv
    co
    cre
    cfv
    #
    cle
    wbr
    wa
    @41
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    cR
    @39
    vk
    cc0
    cc0
    c1
    cn0
    nn0uz
    1e0p1
    @10
    c1
    wceq
    #
    @11
    ci
    @15
    @44
    cmul
    @46
    @11
    ci
    c1
    cexp
    co
    #
    ci
    @10
    c1
    ci
    cexp
    oveq2
    @27
    @47
    ci
    wceq
    ax-icn
    ci
    exp1
    ax-mp
    #
    syl6eq
    vx
    cA
    cB
    ci
    vk
    c1
    @48
    itgvallem
    oveq12d
    @31
    wph
    cc0
    cc0
    cfz
    co
    @16
    vk
    csu
    #
    cR
    wceq
    cc0
    cn0
    wcel
    wph
    @49
    c1
    vx
    cr
    @12
    cc0
    cB
    c1
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    wa
    @51
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    cR
    wph
    cc0
    cz
    wcel
    @55
    cc
    wcel
    @49
    @55
    wceq
    0z
    wph
    @55
    cR
    cc
    wph
    c1
    cR
    cmul
    co
    @55
    cR
    wph
    cR
    @54
    c1
    cmul
    wph
    @54
    vx
    cr
    @12
    cc0
    cB
    cre
    cfv
    #
    cle
    wbr
    wa
    @56
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cR
    wph
    @53
    @58
    citg2
    wph
    vx
    cr
    @52
    @57
    wph
    vx
    cA
    @51
    @56
    @30
    @50
    cB
    cre
    @30
    cB
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    #
    @59
    cmbf
    wcel
    #
    itgcnlem.i
    @59
    iblmbf
    syl
    itgcnlem.v
    mbfmptcl
    #
    div1d
    fveq2d
    ibllem
    mpteq2dv
    fveq2d
    itgcnlem.r
    syl6reqr
    oveq2d
    wph
    cR
    wph
    cR
    wph
    cR
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    wph
    @61
    @63
    @64
    wa
    #
    cT
    cr
    wcel
    #
    cU
    cr
    wcel
    #
    wa
    #
    wph
    @60
    @61
    @65
    @68
    w3a
    itgcnlem.i
    wph
    vx
    cA
    cB
    cR
    cS
    cT
    cU
    cV
    itgcnlem.r
    itgcnlem.s
    itgcnlem.t
    itgcnlem.u
    itgcnlem.v
    iblcnlem
    mpbid
    #
    simp2d
    #
    simpld
    recnd
    #
    mulid2d
    eqtr3d
    #
    @71
    eqeltrd
    @16
    @55
    vk
    cc0
    @10
    cc0
    wceq
    #
    @11
    c1
    @15
    @54
    cmul
    @73
    @11
    ci
    cc0
    cexp
    co
    #
    c1
    @10
    cc0
    ci
    cexp
    oveq2
    @27
    @74
    c1
    wceq
    ax-icn
    ci
    exp0
    ax-mp
    #
    syl6eq
    vx
    cA
    cB
    c1
    vk
    cc0
    @75
    itgvallem
    oveq12d
    fsum1
    sylancr
    @72
    eqtrd
    0nn0
    jctil
    wph
    @45
    @2
    cR
    caddc
    wph
    @44
    cT
    ci
    cmul
    wph
    cT
    vx
    cr
    @12
    cc0
    cB
    cim
    cfv
    #
    cle
    wbr
    wa
    @76
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @44
    itgcnlem.t
    wph
    @78
    @43
    citg2
    wph
    vx
    cr
    @77
    @42
    wph
    vx
    cA
    @76
    @41
    @30
    cB
    cc
    wcel
    #
    @76
    @41
    wceq
    @62
    cB
    imval
    syl
    ibllem
    mpteq2dv
    fveq2d
    syl5req
    oveq2d
    oveq2d
    fsump1i
    wph
    @39
    @38
    caddc
    co
    @39
    cS
    cneg
    #
    caddc
    co
    @39
    cS
    cmin
    co
    @3
    wph
    @38
    @80
    @39
    caddc
    wph
    @32
    cS
    cmul
    co
    @38
    @80
    wph
    cS
    @37
    @32
    cmul
    wph
    cS
    vx
    cr
    @12
    cc0
    @56
    cneg
    #
    cle
    wbr
    wa
    @81
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @37
    itgcnlem.s
    wph
    @83
    @36
    citg2
    wph
    vx
    cr
    @82
    @35
    wph
    vx
    cA
    @81
    @34
    @30
    cB
    cneg
    #
    cre
    cfv
    @81
    @34
    @30
    cB
    @62
    renegd
    @30
    @84
    @33
    cre
    @30
    @84
    @32
    cneg
    #
    cdiv
    co
    #
    @84
    @33
    @30
    @86
    @84
    c1
    cdiv
    co
    @84
    @85
    c1
    @84
    cdiv
    c1
    ax-1cn
    negnegi
    oveq2i
    @30
    @84
    @30
    cB
    @62
    negcld
    #
    div1d
    syl5eq
    @30
    @79
    @86
    @33
    wceq
    #
    @62
    @79
    @32
    cc
    wcel
    @32
    cc0
    wne
    @88
    c1
    ax-1cn
    negcli
    neg1ne0
    cB
    @32
    div2neg
    mp3an23
    syl
    eqtr3d
    fveq2d
    eqtr3d
    ibllem
    mpteq2dv
    fveq2d
    syl5eq
    oveq2d
    wph
    cS
    wph
    cS
    wph
    @63
    @64
    @70
    simprd
    recnd
    #
    mulm1d
    eqtr3d
    oveq2d
    wph
    @39
    cS
    wph
    cR
    @2
    @71
    wph
    @27
    cT
    cc
    wcel
    @2
    cc
    wcel
    ax-icn
    wph
    cT
    wph
    @66
    @67
    wph
    @61
    @65
    @68
    @69
    simp3d
    #
    simpld
    recnd
    #
    ci
    cT
    mulcl
    sylancr
    #
    addcld
    @89
    negsubd
    wph
    cR
    @2
    cS
    @71
    @92
    @89
    addsubd
    3eqtrd
    fsump1i
    wph
    @24
    @5
    @3
    caddc
    wph
    @18
    cU
    cmul
    co
    #
    @24
    @5
    wph
    cU
    @23
    @18
    cmul
    wph
    cU
    vx
    cr
    @12
    cc0
    @76
    cneg
    #
    cle
    wbr
    wa
    @94
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    @23
    itgcnlem.u
    wph
    @96
    @22
    citg2
    wph
    vx
    cr
    @95
    @21
    wph
    vx
    cA
    @94
    @20
    @30
    @84
    cim
    cfv
    #
    @84
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    @94
    @20
    @30
    @84
    cc
    wcel
    @97
    @99
    wceq
    @87
    @84
    imval
    syl
    @30
    cB
    @62
    imnegd
    @30
    @98
    @19
    cre
    @30
    @98
    @84
    @18
    cneg
    #
    cdiv
    co
    #
    @19
    ci
    @100
    @84
    cdiv
    @100
    ci
    ci
    ax-icn
    negnegi
    eqcomi
    oveq2i
    @30
    @79
    @101
    @19
    wceq
    #
    @62
    @79
    @18
    cc
    wcel
    @18
    cc0
    wne
    @102
    ci
    ax-icn
    negcli
    ci
    ax-icn
    ine0
    negne0i
    cB
    @18
    div2neg
    mp3an23
    syl
    syl5eq
    fveq2d
    3eqtr3d
    ibllem
    mpteq2dv
    fveq2d
    syl5eq
    oveq2d
    wph
    @27
    cU
    cc
    wcel
    @93
    @5
    wceq
    ax-icn
    wph
    cU
    wph
    @66
    @67
    @90
    simprd
    recnd
    #
    ci
    cU
    mulneg12
    sylancr
    eqtr3d
    oveq2d
    fsump1i
    simprd
    syl5eq
    wph
    @1
    @2
    @5
    wph
    cR
    cS
    @71
    @89
    subcld
    @92
    wph
    @27
    @4
    cc
    wcel
    @5
    cc
    wcel
    ax-icn
    wph
    cU
    @103
    negcld
    #
    ci
    @4
    mulcl
    sylancr
    addassd
    wph
    @7
    @9
    @1
    caddc
    wph
    ci
    cT
    @4
    caddc
    co
    #
    cmul
    co
    @7
    @9
    wph
    ci
    cT
    @4
    @28
    @91
    @104
    adddid
    wph
    @105
    @8
    ci
    cmul
    wph
    cT
    cU
    @91
    @103
    negsubd
    oveq2d
    eqtr3d
    oveq2d
    3eqtrd
end
