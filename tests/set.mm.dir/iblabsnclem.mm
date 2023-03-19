include "cmbf.mm"
include "wcel.mm"
include "citg2.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cabs.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cibl.mm"
include "w3a.mm"
include "iblrelem.mm"
include "mpbid.mm"
include "simp1d.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "syl.mm"
include "rembl.mm"
include "a1i.mm"
include "recnd.mm"
include "abscld.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalse.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "eqid.mm"
include "fmptd.mm"
include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cmnf.mm"
include "cun.mm"
include "crab.mm"
include "wo.mm"
include "clt.mm"
include "adantlr.mm"
include "biantrurd.mm"
include "simplr.mm"
include "absled.mm"
include "notbid.mm"
include "ltnled.mm"
include "cxr.mm"
include "wb.mm"
include "renegcl.mm"
include "rexrd.mm"
include "ad2antlr.mm"
include "elioomnf.mm"
include "renegcld.mm"
include "3bitr2d.mm"
include "rexr.mm"
include "elioopnf.mm"
include "orbi12d.mm"
include "ianor.mm"
include "syl6bbr.mm"
include "3bitr4rd.mm"
include "rabbidva.mm"
include "mptpreima.mm"
include "uneq12i.mm"
include "unrab.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "wf.mm"
include "iblmbf.mm"
include "mbfima.mm"
include "unmbl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "absltd.mm"
include "bitrd.mm"
include "3anass.mm"
include "elioo2.mm"
include "bitr4d.mm"
include "ismbf2d.mm"
include "syl5eqel.mm"
include "mbfss.mm"
include "caddc.mm"
include "cof.mm"
include "cvv.mm"
include "cico.mm"
include "reex.mm"
include "ifan.mm"
include "max1.mm"
include "sylancr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "0e0icopnf.mm"
include "ifclda.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq12i.mm"
include "max0add.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "00id.mm"
include "3eqtr4a.mm"
include "pm2.61d1.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "ibar.mm"
include "ifbid.mm"
include "mbfpos.mm"
include "syl5eqelr.mm"
include "simp2d.mm"
include "simp3d.mm"
include "itg2addnc.mm"
include "readdcld.mm"
include "jca.mm"

theorem iblabsnclem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vy: setvar y
  assume iblabsnc.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume iblabsnc.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume iblabsnclem.1: |- G = ( x e. RR |-> if ( x e. A , ( abs ` ( F ` B ) ) , 0 ) )
  assume iblabsnclem.2: |- ( ph -> ( x e. A |-> ( F ` B ) ) e. L^1 )
  assume iblabsnclem.3: |- ( ( ph /\ x e. A ) -> ( F ` B ) e. RR )

  disjoint A x
  disjoint ph x
  disjoint G y
  disjoint F y
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint B y
  disjoint V y
  assert |- ( ph -> ( G e. MblFn /\ ( S.2 ` G ) e. RR ) )

  proof
    wph
    cG
    cmbf
    wcel
    cG
    citg2
    cfv
    #
    cr
    wcel
    wph
    cG
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cF
    cfv
    #
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cmbf
    iblabsnclem.1
    wph
    vx
    cA
    cr
    @5
    cr
    wph
    cA
    cvol
    cdm
    #
    wcel
    cA
    cr
    wss
    wph
    vx
    cA
    @3
    cr
    wph
    vx
    cA
    @3
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cr
    @2
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @3
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vx
    cr
    @2
    cc0
    @3
    cneg
    #
    cle
    wbr
    #
    wa
    @16
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    wph
    @8
    cibl
    wcel
    #
    @9
    @15
    @21
    w3a
    iblabsnclem.2
    wph
    vx
    cA
    @3
    iblabsnclem.3
    iblrelem
    mpbid
    #
    simp1d
    #
    iblabsnclem.3
    mbfdm2
    #
    cA
    mblss
    syl
    #
    cr
    @7
    wcel
    wph
    rembl
    a1i
    #
    wph
    @2
    wa
    #
    @4
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @5
    cr
    wcel
    @28
    @3
    @28
    @3
    iblabsnclem.3
    recnd
    abscld
    #
    0re
    @2
    @4
    cc0
    cr
    ifcl
    sylancl
    wph
    @1
    cr
    cA
    cdif
    wcel
    #
    wa
    #
    @2
    wn
    #
    @5
    cc0
    wceq
    @32
    @34
    wph
    @1
    cr
    cA
    eldifn
    adantl
    #
    @2
    @4
    cc0
    iffalse
    #
    syl
    wph
    vx
    cA
    @5
    cmpt
    vx
    cA
    @4
    cmpt
    #
    cmbf
    vx
    cA
    @5
    @4
    @2
    @4
    cc0
    iftrue
    #
    mpteq2ia
    wph
    vy
    cA
    @37
    wph
    vx
    cA
    @4
    cr
    @37
    @31
    @37
    eqid
    #
    fmptd
    @25
    wph
    vy
    cv
    #
    cr
    wcel
    #
    wa
    #
    @37
    ccnv
    #
    @40
    cpnf
    cioo
    co
    #
    cima
    #
    @8
    ccnv
    #
    cmnf
    @40
    cneg
    #
    cioo
    co
    #
    cima
    #
    @46
    @44
    cima
    #
    cun
    #
    @7
    @42
    @4
    @44
    wcel
    #
    vx
    cA
    crab
    @3
    @48
    wcel
    #
    @3
    @44
    wcel
    #
    wo
    #
    vx
    cA
    crab
    #
    @45
    @51
    @42
    @52
    @55
    vx
    cA
    @42
    @2
    wa
    #
    @40
    @4
    clt
    wbr
    #
    @29
    @58
    wa
    #
    @55
    @52
    @57
    @29
    @58
    wph
    @2
    @29
    @41
    @31
    adantlr
    #
    biantrurd
    @57
    @4
    @40
    cle
    wbr
    #
    wn
    @47
    @3
    cle
    wbr
    #
    @3
    @40
    cle
    wbr
    #
    wa
    #
    wn
    #
    @58
    @55
    @57
    @61
    @64
    @57
    @3
    @40
    wph
    @2
    @3
    cr
    wcel
    #
    @41
    iblabsnclem.3
    adantlr
    #
    wph
    @41
    @2
    simplr
    #
    absled
    notbid
    @57
    @40
    @4
    @68
    @60
    ltnled
    @57
    @55
    @62
    wn
    #
    @63
    wn
    #
    wo
    @65
    @57
    @53
    @69
    @54
    @70
    @57
    @53
    @66
    @3
    @47
    clt
    wbr
    #
    wa
    #
    @71
    @69
    @57
    @47
    cxr
    wcel
    #
    @53
    @72
    wb
    @41
    @73
    wph
    @2
    @41
    @47
    @40
    renegcl
    rexrd
    #
    ad2antlr
    @47
    @3
    elioomnf
    syl
    @57
    @66
    @71
    @67
    biantrurd
    @57
    @3
    @47
    @67
    @57
    @40
    @68
    renegcld
    ltnled
    3bitr2d
    @57
    @54
    @66
    @40
    @3
    clt
    wbr
    #
    wa
    #
    @75
    @70
    @57
    @40
    cxr
    wcel
    #
    @54
    @76
    wb
    @41
    @77
    wph
    @2
    @40
    rexr
    #
    ad2antlr
    #
    @40
    @3
    elioopnf
    syl
    @57
    @66
    @75
    @67
    biantrurd
    @57
    @40
    @3
    @68
    @67
    ltnled
    3bitr2d
    orbi12d
    @62
    @63
    ianor
    syl6bbr
    3bitr4rd
    @57
    @77
    @52
    @59
    wb
    @79
    @40
    @4
    elioopnf
    syl
    3bitr4rd
    rabbidva
    vx
    cA
    @4
    @44
    @37
    @39
    mptpreima
    @51
    @53
    vx
    cA
    crab
    #
    @54
    vx
    cA
    crab
    #
    cun
    @56
    @49
    @80
    @50
    @81
    vx
    cA
    @3
    @48
    @8
    @8
    eqid
    #
    mptpreima
    vx
    cA
    @3
    @44
    @8
    @82
    mptpreima
    uneq12i
    @53
    @54
    vx
    cA
    unrab
    eqtri
    3eqtr4g
    wph
    @51
    @7
    wcel
    #
    @41
    wph
    @9
    cA
    cr
    @8
    wf
    #
    @83
    wph
    @22
    @9
    iblabsnclem.2
    @8
    iblmbf
    syl
    #
    wph
    vx
    cA
    @3
    cr
    @8
    iblabsnclem.3
    @82
    fmptd
    #
    @9
    @84
    wa
    @49
    @7
    wcel
    @50
    @7
    wcel
    @83
    cA
    cmnf
    @47
    @8
    mbfima
    cA
    @40
    cpnf
    @8
    mbfima
    @49
    @50
    unmbl
    syl2anc
    syl2anc
    adantr
    eqeltrd
    @42
    @43
    cmnf
    @40
    cioo
    co
    #
    cima
    #
    @46
    @47
    @40
    cioo
    co
    #
    cima
    #
    @7
    @42
    @4
    @87
    wcel
    #
    vx
    cA
    crab
    @3
    @89
    wcel
    #
    vx
    cA
    crab
    @88
    @90
    @42
    @91
    @92
    vx
    cA
    @57
    @91
    @66
    @47
    @3
    clt
    wbr
    #
    @3
    @40
    clt
    wbr
    #
    w3a
    #
    @92
    @57
    @91
    @66
    @93
    @94
    wa
    #
    wa
    #
    @95
    @57
    @91
    @96
    @97
    @57
    @91
    @29
    @4
    @40
    clt
    wbr
    #
    wa
    #
    @98
    @96
    @57
    @77
    @91
    @99
    wb
    @79
    @40
    @4
    elioomnf
    syl
    @57
    @29
    @98
    @60
    biantrurd
    @57
    @3
    @40
    @67
    @68
    absltd
    3bitr2d
    @57
    @66
    @96
    @67
    biantrurd
    bitrd
    @66
    @93
    @94
    3anass
    syl6bbr
    @41
    @92
    @95
    wb
    #
    wph
    @2
    @41
    @73
    @77
    @100
    @74
    @78
    @47
    @40
    @3
    elioo2
    syl2anc
    ad2antlr
    bitr4d
    rabbidva
    vx
    cA
    @4
    @87
    @37
    @39
    mptpreima
    vx
    cA
    @3
    @89
    @8
    @82
    mptpreima
    3eqtr4g
    wph
    @90
    @7
    wcel
    #
    @41
    wph
    @9
    @84
    @101
    @85
    @86
    cA
    @47
    @40
    @8
    mbfima
    syl2anc
    adantr
    eqeltrd
    ismbf2d
    syl5eqel
    mbfss
    syl5eqel
    wph
    @0
    @14
    @20
    caddc
    co
    #
    cr
    wph
    @0
    @13
    @19
    caddc
    cof
    co
    #
    citg2
    cfv
    @102
    wph
    cG
    @103
    citg2
    wph
    @103
    @6
    cG
    wph
    @103
    vx
    cr
    @12
    @18
    caddc
    co
    #
    cmpt
    @6
    wph
    vx
    cr
    @12
    @18
    caddc
    @13
    @19
    cvv
    cc0
    cpnf
    cico
    co
    #
    @105
    cr
    cvv
    wcel
    wph
    reex
    a1i
    wph
    @12
    @105
    wcel
    #
    @1
    cr
    wcel
    #
    wph
    @12
    @2
    @10
    @3
    cc0
    cif
    #
    cc0
    cif
    #
    @105
    @2
    @10
    @3
    cc0
    ifan
    #
    wph
    @2
    @108
    cc0
    @105
    @28
    @108
    cr
    wcel
    #
    cc0
    @108
    cle
    wbr
    #
    @108
    @105
    wcel
    @28
    @66
    @30
    @111
    iblabsnclem.3
    0re
    @10
    @3
    cc0
    cr
    ifcl
    sylancl
    @28
    @30
    @66
    @112
    0re
    iblabsnclem.3
    cc0
    @3
    max1
    sylancr
    @108
    elrege0
    sylanbrc
    cc0
    @105
    wcel
    wph
    @34
    wa
    0e0icopnf
    a1i
    #
    ifclda
    syl5eqel
    #
    adantr
    #
    wph
    @18
    @105
    wcel
    @107
    wph
    @18
    @2
    @17
    @16
    cc0
    cif
    #
    cc0
    cif
    #
    @105
    @2
    @17
    @16
    cc0
    ifan
    #
    wph
    @2
    @116
    cc0
    @105
    @28
    @116
    cr
    wcel
    #
    cc0
    @116
    cle
    wbr
    #
    @116
    @105
    wcel
    @28
    @16
    cr
    wcel
    #
    @30
    @119
    @28
    @3
    iblabsnclem.3
    renegcld
    #
    0re
    @17
    @16
    cc0
    cr
    ifcl
    sylancl
    @28
    @30
    @121
    @120
    0re
    @122
    cc0
    @16
    max1
    sylancr
    @116
    elrege0
    sylanbrc
    @113
    ifclda
    syl5eqel
    adantr
    #
    wph
    @13
    eqidd
    wph
    @19
    eqidd
    offval2
    wph
    vx
    cr
    @104
    @5
    wph
    @104
    @109
    @117
    caddc
    co
    #
    @5
    @12
    @109
    @18
    @117
    caddc
    @110
    @118
    oveq12i
    wph
    @2
    @124
    @5
    wceq
    #
    wph
    @2
    @125
    @28
    @108
    @116
    caddc
    co
    #
    @4
    @124
    @5
    @28
    @66
    @126
    @4
    wceq
    iblabsnclem.3
    @3
    max0add
    syl
    @28
    @109
    @108
    @117
    @116
    caddc
    @2
    @109
    @108
    wceq
    wph
    @2
    @108
    cc0
    iftrue
    adantl
    @2
    @117
    @116
    wceq
    wph
    @2
    @116
    cc0
    iftrue
    adantl
    oveq12d
    @2
    @5
    @4
    wceq
    wph
    @38
    adantl
    3eqtr4d
    ex
    @34
    cc0
    cc0
    caddc
    co
    cc0
    @124
    @5
    00id
    @34
    @109
    cc0
    @117
    cc0
    caddc
    @2
    @108
    cc0
    iffalse
    #
    @2
    @116
    cc0
    iffalse
    oveq12d
    @36
    3eqtr4a
    pm2.61d1
    syl5eq
    mpteq2dv
    eqtrd
    iblabsnclem.1
    syl6reqr
    fveq2d
    wph
    @13
    @19
    wph
    vx
    cA
    cr
    @12
    @105
    @26
    @27
    wph
    @106
    @2
    @114
    adantr
    @33
    @34
    @12
    cc0
    wceq
    @35
    @34
    @12
    @109
    cc0
    @110
    @127
    syl5eq
    syl
    wph
    vx
    cA
    @12
    cmpt
    vx
    cA
    @108
    cmpt
    cmbf
    vx
    cA
    @108
    @12
    @2
    @10
    @11
    @3
    cc0
    @2
    @10
    ibar
    ifbid
    mpteq2ia
    wph
    vx
    cA
    @3
    iblabsnclem.3
    @24
    mbfpos
    syl5eqelr
    mbfss
    wph
    vx
    cr
    @12
    @105
    @13
    @115
    @13
    eqid
    fmptd
    wph
    @9
    @15
    @21
    @23
    simp2d
    #
    wph
    vx
    cr
    @18
    @105
    @19
    @123
    @19
    eqid
    fmptd
    wph
    @9
    @15
    @21
    @23
    simp3d
    #
    itg2addnc
    eqtrd
    wph
    @14
    @20
    @128
    @129
    readdcld
    eqeltrd
    jca
end
