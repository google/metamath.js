include "citg1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "crp.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cdiv.mm"
include "cr.mm"
include "itg2monolem2.mm"
include "adantr.mm"
include "recnd.mm"
include "cdm.mm"
include "itg1cl.mm"
include "syl.mm"
include "simpr.mm"
include "rpred.mm"
include "readdcld.mm"
include "cc0.mm"
include "0red.mm"
include "c1.mm"
include "citg2.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "cn.mm"
include "1nn.mm"
include "cico.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "feq1d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "itg2cl.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "supxrcl.mm"
include "syl5eqel.mm"
include "itg2ge0.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "syl5eqelr.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "syl6breqr.mm"
include "xrletrd.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "gt0ne0d.mm"
include "div23d.mm"
include "c2.mm"
include "cif.mm"
include "redivcld.mm"
include "remulcld.mm"
include "halfre.mm"
include "ifcl.mm"
include "max2.mm"
include "sylancr.mm"
include "wb.mm"
include "wn.mm"
include "rexrd.mm"
include "xrltnle.mm"
include "mpbird.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "crab.mm"
include "cmbf.mm"
include "adantlr.mm"
include "cofr.mm"
include "wrex.mm"
include "cioo.mm"
include "halfgt0.mm"
include "max1.mm"
include "ltletrd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1red.mm"
include "ltdivmul.mm"
include "halflt1.mm"
include "breq1.mm"
include "ifboth.mm"
include "w3a.mm"
include "1re.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "cbvrabv.mm"
include "mpteq2i.mm"
include "itg2monolem1.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "ledivmul2.mm"
include "mulgt0d.mm"
include "lemul2.mm"
include "alrple.mm"

theorem itg2monolem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let cA: class A
  let vf: setvar f
  let vm: setvar m
  let vt: setvar t
  let vz: setvar z
  let vw: setvar w
  let cH: class H
  let cT: class T
  assume itg2mono.1: |- G = ( x e. RR |-> sup ( ran ( n e. NN |-> ( ( F ` n ) ` x ) ) , RR , < ) )
  assume itg2mono.2: |- ( ( ph /\ n e. NN ) -> ( F ` n ) e. MblFn )
  assume itg2mono.3: |- ( ( ph /\ n e. NN ) -> ( F ` n ) : RR --> ( 0 [,) +oo ) )
  assume itg2mono.4: |- ( ( ph /\ n e. NN ) -> ( F ` n ) oR <_ ( F ` ( n + 1 ) ) )
  assume itg2mono.5: |- ( ( ph /\ x e. RR ) -> E. y e. RR A. n e. NN ( ( F ` n ) ` x ) <_ y )
  assume itg2mono.6: |- S = sup ( ran ( n e. NN |-> ( S.2 ` ( F ` n ) ) ) , RR* , < )
  assume itg2monolem2.7: |- ( ph -> P e. dom S.1 )
  assume itg2monolem2.8: |- ( ph -> P oR <_ G )
  assume itg2monolem2.9: |- ( ph -> -. ( S.1 ` P ) <_ S )

  disjoint n x
  disjoint n y
  disjoint G n
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint m n
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n t
  disjoint n z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint j n
  disjoint j w
  disjoint j y
  disjoint H j
  disjoint k n
  disjoint k w
  disjoint k y
  disjoint H k
  disjoint n w
  disjoint H n
  disjoint w x
  disjoint w y
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint P t
  disjoint j m
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k z
  disjoint F k
  disjoint m w
  disjoint F m
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint f ph
  disjoint j t
  disjoint j ph
  disjoint k t
  disjoint k ph
  disjoint m ph
  disjoint t w
  disjoint ph t
  disjoint ph w
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S t
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint T w
  disjoint T x
  disjoint T y
  assert |- ( ph -> ( S.1 ` P ) <_ S )

  proof
    wph
    cP
    citg1
    cfv
    #
    cS
    cle
    wbr
    #
    @0
    cS
    vt
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vt
    crp
    wral
    #
    wph
    @4
    vt
    crp
    wph
    @2
    crp
    wcel
    #
    wa
    #
    @4
    cS
    @0
    cmul
    co
    #
    cS
    @3
    cmul
    co
    cle
    wbr
    #
    @7
    @8
    @3
    cdiv
    co
    #
    cS
    cle
    wbr
    #
    @9
    @7
    @10
    cS
    @3
    cdiv
    co
    #
    @0
    cmul
    co
    #
    cS
    cle
    @7
    cS
    @0
    @3
    @7
    cS
    wph
    cS
    cr
    wcel
    #
    @6
    wph
    vx
    vy
    cP
    cS
    vn
    cF
    cG
    itg2mono.1
    itg2mono.2
    itg2mono.3
    itg2mono.4
    itg2mono.5
    itg2mono.6
    itg2monolem2.7
    itg2monolem2.8
    itg2monolem2.9
    itg2monolem2
    #
    adantr
    #
    recnd
    @7
    @0
    @7
    cP
    citg1
    cdm
    wcel
    #
    @0
    cr
    wcel
    #
    wph
    @17
    @6
    itg2monolem2.7
    adantr
    #
    cP
    itg1cl
    #
    syl
    #
    recnd
    @7
    @3
    @7
    cS
    @2
    @16
    @7
    @2
    wph
    @6
    simpr
    #
    rpred
    readdcld
    #
    recnd
    #
    @7
    @3
    @7
    cc0
    cS
    @3
    @7
    0red
    #
    @16
    @23
    wph
    cc0
    cS
    cle
    wbr
    @6
    wph
    cc0
    c1
    cF
    cfv
    #
    citg2
    cfv
    #
    cS
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    @26
    wf
    #
    @27
    cxr
    wcel
    c1
    cn
    wcel
    #
    wph
    cr
    @29
    vn
    cv
    #
    cF
    cfv
    #
    wf
    #
    vn
    cn
    wral
    @30
    1nn
    wph
    @34
    vn
    cn
    wph
    @32
    cn
    wcel
    #
    wa
    #
    cr
    cc0
    cpnf
    cico
    co
    #
    @33
    wf
    #
    @37
    @29
    wss
    @34
    itg2mono.3
    cc0
    cpnf
    icossicc
    cr
    @37
    @29
    @33
    fss
    sylancl
    #
    ralrimiva
    @34
    @30
    vn
    c1
    cn
    @32
    c1
    wceq
    #
    cr
    @29
    @33
    @26
    @32
    c1
    cF
    fveq2
    #
    feq1d
    rspcv
    mpsyl
    #
    @26
    itg2cl
    syl
    wph
    cS
    vn
    cn
    @33
    citg2
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cxr
    itg2mono.6
    wph
    @45
    cxr
    wss
    #
    @46
    cxr
    wcel
    wph
    cn
    cxr
    @44
    wf
    #
    @47
    wph
    vn
    cn
    @43
    cxr
    @44
    @36
    @34
    @43
    cxr
    wcel
    @39
    @33
    itg2cl
    syl
    @44
    eqid
    #
    fmptd
    #
    cn
    cxr
    @44
    frn
    syl
    #
    @45
    supxrcl
    syl
    syl5eqel
    #
    wph
    @30
    cc0
    @27
    cle
    wbr
    @42
    @26
    itg2ge0
    syl
    wph
    @27
    @46
    cS
    cle
    wph
    @47
    @27
    @45
    wcel
    @27
    @46
    cle
    wbr
    @51
    wph
    @27
    c1
    @44
    cfv
    #
    @45
    @31
    @53
    @27
    wceq
    1nn
    vn
    c1
    @43
    @27
    cn
    @44
    @40
    @33
    @26
    citg2
    @41
    fveq2d
    @49
    @26
    citg2
    fvex
    fvmpt
    ax-mp
    wph
    @44
    cn
    wfn
    #
    @31
    @53
    @45
    wcel
    wph
    @48
    @54
    @50
    cn
    cxr
    @44
    ffn
    syl
    1nn
    cn
    c1
    @44
    fnfvelrn
    sylancl
    syl5eqelr
    @45
    @27
    supxrub
    syl2anc
    itg2mono.6
    syl6breqr
    xrletrd
    adantr
    #
    @7
    cS
    @2
    @16
    @22
    ltaddrpd
    #
    lelttrd
    #
    gt0ne0d
    #
    div23d
    @7
    @13
    c1
    c2
    cdiv
    co
    #
    @12
    cle
    wbr
    #
    @12
    @59
    cif
    #
    @0
    cmul
    co
    #
    cS
    @7
    @12
    @0
    @7
    cS
    @3
    @16
    @23
    @58
    redivcld
    #
    @21
    remulcld
    @7
    @61
    @0
    @7
    @12
    cr
    wcel
    #
    @59
    cr
    wcel
    #
    @61
    cr
    wcel
    #
    @63
    halfre
    @60
    @12
    @59
    cr
    ifcl
    sylancl
    #
    @21
    remulcld
    #
    @16
    @7
    @12
    @61
    cle
    wbr
    #
    @13
    @62
    cle
    wbr
    #
    @7
    @65
    @64
    @69
    halfre
    @63
    @59
    @12
    max2
    sylancr
    @7
    @64
    @66
    @18
    cc0
    @0
    clt
    wbr
    @69
    @70
    wb
    @63
    @67
    @21
    @7
    cc0
    cS
    @0
    @25
    @16
    @21
    @55
    wph
    cS
    @0
    clt
    wbr
    #
    @6
    wph
    @71
    @1
    wn
    #
    itg2monolem2.9
    wph
    cS
    cxr
    wcel
    @0
    cxr
    wcel
    @71
    @72
    wb
    @52
    wph
    @0
    wph
    @17
    @18
    itg2monolem2.7
    @20
    syl
    #
    rexrd
    cS
    @0
    xrltnle
    syl2anc
    mpbird
    adantr
    lelttrd
    #
    @12
    @61
    @0
    lemul1
    syl112anc
    mpbid
    @7
    vx
    vy
    vn
    cn
    @61
    vy
    cv
    #
    cP
    cfv
    #
    cmul
    co
    #
    @75
    @33
    cfv
    #
    cle
    wbr
    #
    vy
    cr
    crab
    #
    cmpt
    cS
    @61
    vn
    cF
    cG
    cP
    itg2mono.1
    wph
    @35
    @33
    cmbf
    wcel
    @6
    itg2mono.2
    adantlr
    wph
    @35
    @38
    @6
    itg2mono.3
    adantlr
    wph
    @35
    @33
    @32
    c1
    caddc
    co
    cF
    cfv
    cle
    cofr
    #
    wbr
    @6
    itg2mono.4
    adantlr
    wph
    vx
    cv
    #
    cr
    wcel
    @82
    @33
    cfv
    #
    @75
    cle
    wbr
    vn
    cn
    wral
    vy
    cr
    wrex
    @6
    itg2mono.5
    adantlr
    itg2mono.6
    @7
    @66
    cc0
    @61
    clt
    wbr
    #
    @61
    c1
    clt
    wbr
    #
    @61
    cc0
    c1
    cioo
    co
    wcel
    #
    @67
    @7
    cc0
    @59
    @61
    @25
    @65
    @7
    halfre
    a1i
    @67
    cc0
    @59
    clt
    wbr
    @7
    halfgt0
    a1i
    @7
    @65
    @64
    @59
    @61
    cle
    wbr
    halfre
    @63
    @59
    @12
    max1
    sylancr
    ltletrd
    #
    @7
    @12
    c1
    clt
    wbr
    #
    @59
    c1
    clt
    wbr
    #
    @85
    @7
    @88
    cS
    @3
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @7
    cS
    @3
    @90
    clt
    @56
    @7
    @3
    @24
    mulid1d
    breqtrrd
    @7
    @14
    c1
    cr
    wcel
    @3
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    @88
    @91
    wb
    @16
    @7
    1red
    @23
    @57
    cS
    c1
    @3
    ltdivmul
    syl112anc
    mpbird
    halflt1
    @60
    @88
    @89
    @85
    @12
    @59
    @12
    @61
    c1
    clt
    breq1
    @59
    @61
    c1
    clt
    breq1
    ifboth
    sylancl
    @28
    c1
    cxr
    wcel
    @86
    @66
    @84
    @85
    w3a
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    @61
    elioo2
    mp2an
    syl3anbrc
    @19
    wph
    cP
    cG
    @81
    wbr
    @6
    itg2monolem2.8
    adantr
    @16
    vn
    cn
    @80
    @61
    @82
    cP
    cfv
    #
    cmul
    co
    #
    @83
    cle
    wbr
    #
    vx
    cr
    crab
    @79
    @96
    vy
    vx
    cr
    @75
    @82
    wceq
    #
    @77
    @95
    @78
    @83
    cle
    @97
    @76
    @94
    @61
    cmul
    @75
    @82
    cP
    fveq2
    oveq2d
    @75
    @82
    @33
    fveq2
    breq12d
    cbvrabv
    mpteq2i
    itg2monolem1
    #
    letrd
    eqbrtrd
    @7
    @8
    cr
    wcel
    @14
    @92
    @93
    @11
    @9
    wb
    @7
    cS
    @0
    @16
    @21
    remulcld
    @16
    @23
    @57
    @8
    cS
    @3
    ledivmul2
    syl112anc
    mpbid
    @7
    @18
    @92
    @14
    cc0
    cS
    clt
    wbr
    @4
    @9
    wb
    @21
    @23
    @16
    @7
    cc0
    @62
    cS
    @25
    @68
    @16
    @7
    @61
    @0
    @67
    @21
    @87
    @74
    mulgt0d
    @98
    ltletrd
    @0
    @3
    cS
    lemul2
    syl112anc
    mpbird
    ralrimiva
    wph
    @18
    @14
    @1
    @5
    wb
    @73
    @15
    vt
    @0
    cS
    alrple
    syl2anc
    mpbird
end
