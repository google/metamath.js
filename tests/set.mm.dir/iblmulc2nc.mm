include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "ci.mm"
include "cexp.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "cabs.mm"
include "cim.mm"
include "caddc.mm"
include "ifan.mm"
include "cxr.mm"
include "cc.mm"
include "adantr.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "mulcld.mm"
include "adantlr.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad2antlr.mm"
include "wne.mm"
include "ax-icn.mm"
include "ine0.mm"
include "expclz.mm"
include "mp3an12.mm"
include "expne0i.mm"
include "divcld.mm"
include "recld.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "rexrd.mm"
include "max1.mm"
include "sylancr.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "fmptd.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cico.mm"
include "recnd.mm"
include "abscld.mm"
include "imcld.mm"
include "readdcld.mm"
include "absge0d.mm"
include "addge0d.mm"
include "elrege0.mm"
include "0e0icopnf.mm"
include "cvv.mm"
include "reex.mm"
include "eqidd.mm"
include "offval2.mm"
include "wceq.mm"
include "iftrue.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "00id.mm"
include "iffalse.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "mpteq2i.mm"
include "syl6req.mm"
include "fveq2d.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "iblabsnclem.mm"
include "simprd.mm"
include "itg2addnc.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "itg2mulc.mm"
include "fconstmpt.mm"
include "oveq2d.mm"
include "adantl.mm"
include "mul01d.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"
include "mpteq2dv.mm"
include "3eqtr3d.mm"
include "remulcld.mm"
include "cofr.mm"
include "mulge0d.mm"
include "ad2antrr.mm"
include "releabsd.mm"
include "c1.mm"
include "absdivd.mm"
include "cn0.mm"
include "elfznn0.mm"
include "absexp.mm"
include "absi.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl5eq.mm"
include "div1d.mm"
include "3eqtrd.mm"
include "absmuld.mm"
include "breqtrd.mm"
include "mulcl.mm"
include "abstrid.mm"
include "replimd.mm"
include "absmul.mm"
include "syl6eq.mm"
include "mulid2d.mm"
include "eqtr2d.mm"
include "3brtr4d.mm"
include "lemul2ad.mm"
include "letrd.mm"
include "breq1.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "ex.mm"
include "0le0.mm"
include "pm2.61d1.mm"
include "syl5eqbr.mm"
include "ralrimivw.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"
include "ralrimiva.mm"
include "isibl2.mm"
include "mpbir2and.mm"

theorem iblmulc2nc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume itgmulc2nc.1: |- ( ph -> C e. CC )
  assume itgmulc2nc.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgmulc2nc.3: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgmulc2nc.m: |- ( ph -> ( x e. A |-> ( C x. B ) ) e. MblFn )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> ( x e. A |-> ( C x. B ) ) e. L^1 )

  proof
    wph
    vx
    cA
    cC
    cB
    cmul
    co
    #
    cmpt
    #
    cibl
    wcel
    @1
    cmbf
    wcel
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    @0
    ci
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    @7
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
    vk
    cc0
    c3
    cfz
    co
    #
    wral
    itgmulc2nc.m
    wph
    @12
    vk
    @13
    wph
    @4
    @13
    wcel
    #
    wa
    #
    cr
    cc0
    cpnf
    cicc
    co
    #
    @10
    wf
    #
    vx
    cr
    @3
    cC
    cabs
    cfv
    #
    cB
    cre
    cfv
    #
    cabs
    cfv
    #
    cB
    cim
    cfv
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
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
    @11
    @27
    cle
    wbr
    #
    @12
    @15
    vx
    cr
    @9
    @16
    @10
    @15
    @2
    cr
    wcel
    #
    wa
    @9
    @3
    @8
    @7
    cc0
    cif
    #
    cc0
    cif
    #
    @16
    @3
    @8
    @7
    cc0
    ifan
    #
    @15
    @32
    @16
    wcel
    @30
    @15
    @3
    @31
    cc0
    @16
    @15
    @3
    wa
    #
    @31
    cxr
    wcel
    cc0
    @31
    cle
    wbr
    #
    @31
    @16
    wcel
    @34
    @31
    @34
    @7
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @31
    cr
    wcel
    @34
    @6
    @34
    @0
    @5
    wph
    @3
    @0
    cc
    wcel
    @14
    wph
    @3
    wa
    #
    cC
    cB
    wph
    cC
    cc
    wcel
    @3
    itgmulc2nc.1
    adantr
    #
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
    @40
    cmbf
    wcel
    itgmulc2nc.3
    @40
    iblmbf
    syl
    itgmulc2nc.2
    mbfmptcl
    #
    mulcld
    #
    adantlr
    #
    @34
    @4
    cz
    wcel
    #
    @5
    cc
    wcel
    #
    @14
    @45
    wph
    @3
    @4
    cc0
    c3
    elfzelz
    #
    ad2antlr
    #
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @45
    @46
    ax-icn
    ine0
    ci
    @4
    expclz
    mp3an12
    syl
    #
    @34
    @45
    @5
    cc0
    wne
    #
    @48
    @49
    @50
    @45
    @52
    ax-icn
    ine0
    ci
    @4
    expne0i
    mp3an12
    syl
    #
    divcld
    #
    recld
    #
    0re
    @8
    @7
    cc0
    cr
    ifcl
    sylancl
    rexrd
    @34
    @37
    @36
    @35
    0re
    @55
    cc0
    @7
    max1
    sylancr
    @31
    elxrge0
    sylanbrc
    cc0
    @16
    wcel
    #
    @15
    @3
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    adantr
    syl5eqel
    #
    @10
    eqid
    fmptd
    #
    wph
    @28
    @14
    wph
    @27
    @18
    vx
    cr
    @3
    @20
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    vx
    cr
    @3
    @22
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    cr
    wph
    cr
    @18
    csn
    cxp
    #
    vx
    cr
    @3
    @23
    cc0
    cif
    #
    cmpt
    #
    cmul
    cof
    co
    #
    citg2
    cfv
    @18
    @70
    citg2
    cfv
    #
    cmul
    co
    @27
    @67
    wph
    @18
    @70
    wph
    vx
    cr
    @69
    cc0
    cpnf
    cico
    co
    #
    @70
    wph
    @69
    @73
    wcel
    @30
    wph
    @3
    @23
    cc0
    @73
    @38
    @23
    cr
    wcel
    cc0
    @23
    cle
    wbr
    @23
    @73
    wcel
    @38
    @20
    @22
    @38
    @19
    @38
    @19
    @38
    cB
    @42
    recld
    #
    recnd
    #
    abscld
    #
    @38
    @21
    @38
    @21
    @38
    cB
    @42
    imcld
    #
    recnd
    #
    abscld
    #
    readdcld
    #
    @38
    @20
    @22
    @76
    @79
    @38
    @19
    @75
    absge0d
    #
    @38
    @21
    @78
    absge0d
    #
    addge0d
    #
    @23
    elrege0
    sylanbrc
    cc0
    @73
    wcel
    wph
    @57
    wa
    #
    0e0icopnf
    a1i
    #
    ifclda
    adantr
    #
    @70
    eqid
    fmptd
    wph
    @72
    @66
    cr
    wph
    @72
    @61
    @64
    caddc
    cof
    co
    #
    citg2
    cfv
    @66
    wph
    @70
    @87
    citg2
    wph
    @87
    vx
    cr
    @60
    @63
    caddc
    co
    #
    cmpt
    @70
    wph
    vx
    cr
    @60
    @63
    caddc
    @61
    @64
    cvv
    @73
    @73
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    #
    wph
    @60
    @73
    wcel
    @30
    wph
    @3
    @20
    cc0
    @73
    @38
    @20
    cr
    wcel
    cc0
    @20
    cle
    wbr
    @20
    @73
    wcel
    @76
    @81
    @20
    elrege0
    sylanbrc
    @85
    ifclda
    adantr
    #
    wph
    @63
    @73
    wcel
    @30
    wph
    @3
    @22
    cc0
    @73
    @38
    @22
    cr
    wcel
    cc0
    @22
    cle
    wbr
    @22
    @73
    wcel
    @79
    @82
    @22
    elrege0
    sylanbrc
    @85
    ifclda
    adantr
    #
    wph
    @61
    eqidd
    wph
    @64
    eqidd
    offval2
    vx
    cr
    @88
    @69
    @3
    @88
    @69
    wceq
    @3
    @88
    @23
    @69
    @3
    @60
    @20
    @63
    @22
    caddc
    @3
    @20
    cc0
    iftrue
    @3
    @22
    cc0
    iftrue
    oveq12d
    @3
    @23
    cc0
    iftrue
    #
    eqtr4d
    @57
    cc0
    cc0
    caddc
    co
    cc0
    @88
    @69
    00id
    @57
    @60
    cc0
    @63
    cc0
    caddc
    @3
    @20
    cc0
    iffalse
    @3
    @22
    cc0
    iffalse
    oveq12d
    @3
    @23
    cc0
    iffalse
    #
    3eqtr4a
    pm2.61i
    mpteq2i
    syl6req
    fveq2d
    wph
    @61
    @64
    wph
    @61
    cmbf
    wcel
    #
    @62
    cr
    wcel
    #
    wph
    vx
    cA
    cB
    cre
    @61
    cV
    itgmulc2nc.2
    itgmulc2nc.3
    @61
    eqid
    #
    wph
    vx
    cA
    @19
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @21
    cmpt
    cibl
    wcel
    #
    wph
    @41
    @98
    @99
    wa
    itgmulc2nc.3
    wph
    vx
    cA
    cB
    @42
    iblcn
    mpbid
    #
    simpld
    @74
    iblabsnclem
    #
    simpld
    wph
    vx
    cr
    @60
    @73
    @61
    @91
    @97
    fmptd
    wph
    @95
    @96
    @101
    simprd
    #
    wph
    vx
    cr
    @63
    @73
    @64
    @92
    @64
    eqid
    #
    fmptd
    wph
    @64
    cmbf
    wcel
    @65
    cr
    wcel
    wph
    vx
    cA
    cB
    cim
    @64
    cV
    itgmulc2nc.2
    itgmulc2nc.3
    @103
    wph
    @98
    @99
    @100
    simprd
    @77
    iblabsnclem
    simprd
    #
    itg2addnc
    eqtrd
    #
    wph
    @62
    @65
    @102
    @104
    readdcld
    #
    eqeltrd
    wph
    @18
    cr
    wcel
    #
    cc0
    @18
    cle
    wbr
    #
    @18
    @73
    wcel
    wph
    cC
    itgmulc2nc.1
    abscld
    #
    wph
    cC
    itgmulc2nc.1
    absge0d
    #
    @18
    elrege0
    sylanbrc
    itg2mulc
    wph
    @71
    @26
    citg2
    wph
    @71
    vx
    cr
    @18
    @69
    cmul
    co
    #
    cmpt
    @26
    wph
    vx
    cr
    @18
    @69
    cmul
    @68
    @70
    cvv
    cr
    @73
    @90
    wph
    @107
    @30
    @109
    adantr
    @86
    @68
    vx
    cr
    @18
    cmpt
    wceq
    wph
    vx
    cr
    @18
    fconstmpt
    a1i
    wph
    @70
    eqidd
    offval2
    wph
    vx
    cr
    @111
    @25
    wph
    @3
    @111
    @25
    wceq
    #
    @3
    @112
    wph
    @3
    @111
    @24
    @25
    @3
    @69
    @23
    @18
    cmul
    @93
    oveq2d
    @3
    @24
    cc0
    iftrue
    #
    eqtr4d
    adantl
    @84
    @18
    cc0
    cmul
    co
    #
    cc0
    @111
    @25
    wph
    @114
    cc0
    wceq
    @57
    wph
    @18
    wph
    @18
    @109
    recnd
    mul01d
    adantr
    @84
    @69
    cc0
    @18
    cmul
    @57
    @69
    cc0
    wceq
    wph
    @94
    adantl
    oveq2d
    @57
    @25
    cc0
    wceq
    wph
    @3
    @24
    cc0
    iffalse
    #
    adantl
    3eqtr4d
    pm2.61dan
    mpteq2dv
    eqtrd
    fveq2d
    wph
    @72
    @66
    @18
    cmul
    @105
    oveq2d
    3eqtr3d
    wph
    @18
    @66
    @109
    @106
    remulcld
    eqeltrd
    adantr
    @15
    @17
    cr
    @16
    @26
    wf
    @10
    @26
    cle
    cofr
    wbr
    #
    @29
    @59
    @15
    vx
    cr
    @25
    @16
    @26
    wph
    @25
    @16
    wcel
    @14
    @30
    wph
    @3
    @24
    cc0
    @16
    @38
    @24
    cxr
    wcel
    cc0
    @24
    cle
    wbr
    #
    @24
    @16
    wcel
    @38
    @24
    @38
    @18
    @23
    wph
    @107
    @3
    @109
    adantr
    #
    @80
    remulcld
    #
    rexrd
    @38
    @18
    @23
    @118
    @80
    wph
    @108
    @3
    @110
    adantr
    #
    @83
    mulge0d
    #
    @24
    elxrge0
    sylanbrc
    @56
    @84
    0e0iccpnf
    a1i
    ifclda
    ad2antrr
    #
    @26
    eqid
    fmptd
    @15
    @116
    @9
    @25
    cle
    wbr
    #
    vx
    cr
    wral
    @15
    @123
    vx
    cr
    @15
    @9
    @32
    @25
    cle
    @33
    @15
    @3
    @32
    @25
    cle
    wbr
    #
    @15
    @3
    @124
    @34
    @31
    @24
    @32
    @25
    cle
    @34
    @7
    @24
    cle
    wbr
    #
    @117
    @31
    @24
    cle
    wbr
    #
    @34
    @7
    @18
    cB
    cabs
    cfv
    #
    cmul
    co
    #
    @24
    @55
    wph
    @3
    @128
    cr
    wcel
    @14
    @38
    @18
    @127
    @118
    @38
    cB
    @42
    abscld
    #
    remulcld
    adantlr
    wph
    @3
    @24
    cr
    wcel
    @14
    @119
    adantlr
    @34
    @7
    @6
    cabs
    cfv
    #
    @128
    cle
    @34
    @6
    @54
    releabsd
    @34
    @130
    @0
    cabs
    cfv
    #
    @128
    @34
    @130
    @131
    @5
    cabs
    cfv
    #
    cdiv
    co
    #
    @131
    c1
    cdiv
    co
    #
    @131
    @34
    @0
    @5
    @44
    @51
    @53
    absdivd
    @14
    @133
    @134
    wceq
    wph
    @3
    @14
    @132
    c1
    @131
    cdiv
    @14
    @132
    ci
    cabs
    cfv
    #
    @4
    cexp
    co
    #
    c1
    @14
    @49
    @4
    cn0
    wcel
    @132
    @136
    wceq
    ax-icn
    @4
    c3
    elfznn0
    ci
    @4
    absexp
    sylancr
    @14
    @136
    c1
    @4
    cexp
    co
    #
    c1
    @135
    c1
    @4
    cexp
    absi
    oveq1i
    @14
    @45
    @137
    c1
    wceq
    @47
    @4
    1exp
    syl
    syl5eq
    eqtrd
    oveq2d
    ad2antlr
    @34
    @131
    wph
    @3
    @131
    cc
    wcel
    @14
    @38
    @131
    @38
    @0
    @43
    abscld
    recnd
    adantlr
    div1d
    3eqtrd
    wph
    @3
    @131
    @128
    wceq
    @14
    @38
    cC
    cB
    @39
    @42
    absmuld
    adantlr
    eqtrd
    breqtrd
    wph
    @3
    @128
    @24
    cle
    wbr
    @14
    @38
    @127
    @23
    @18
    @129
    @80
    @118
    @120
    @38
    @19
    ci
    @21
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    @20
    @138
    cabs
    cfv
    #
    caddc
    co
    @127
    @23
    cle
    @38
    @19
    @138
    @75
    @38
    @49
    @21
    cc
    wcel
    #
    @138
    cc
    wcel
    ax-icn
    @78
    ci
    @21
    mulcl
    sylancr
    abstrid
    @38
    cB
    @139
    cabs
    @38
    cB
    @42
    replimd
    fveq2d
    @38
    @22
    @140
    @20
    caddc
    @38
    @140
    c1
    @22
    cmul
    co
    #
    @22
    @38
    @140
    @135
    @22
    cmul
    co
    #
    @142
    @38
    @49
    @141
    @140
    @143
    wceq
    ax-icn
    @78
    ci
    @21
    absmul
    sylancr
    @135
    c1
    @22
    cmul
    absi
    oveq1i
    syl6eq
    @38
    @22
    @38
    @22
    @79
    recnd
    mulid2d
    eqtr2d
    oveq2d
    3brtr4d
    lemul2ad
    adantlr
    letrd
    wph
    @3
    @117
    @14
    @121
    adantlr
    @8
    @125
    @117
    @126
    @7
    cc0
    @7
    @31
    @24
    cle
    breq1
    cc0
    @31
    @24
    cle
    breq1
    ifboth
    syl2anc
    @3
    @32
    @31
    wceq
    @15
    @3
    @31
    cc0
    iftrue
    adantl
    @3
    @25
    @24
    wceq
    @15
    @113
    adantl
    3brtr4d
    ex
    @57
    cc0
    cc0
    @32
    @25
    cle
    cc0
    cc0
    cle
    wbr
    @57
    0le0
    a1i
    @3
    @31
    cc0
    iffalse
    @115
    3brtr4d
    pm2.61d1
    syl5eqbr
    ralrimivw
    @15
    vx
    cr
    @9
    @25
    cle
    @10
    @26
    cvv
    @16
    @16
    @89
    @15
    reex
    a1i
    @58
    @122
    @15
    @10
    eqidd
    @15
    @26
    eqidd
    ofrfval2
    mpbird
    @10
    @26
    itg2le
    syl3anc
    @27
    @10
    itg2lecl
    syl3anc
    ralrimiva
    wph
    vx
    cA
    @0
    @7
    vk
    @10
    cc
    wph
    @10
    eqidd
    @38
    @7
    eqidd
    @43
    isibl2
    mpbir2and
end
