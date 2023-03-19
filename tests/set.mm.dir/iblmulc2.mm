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
include "iblmbf.mm"
include "syl.mm"
include "mbfmulc2.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "cabs.mm"
include "ifan.mm"
include "cxr.mm"
include "cc.mm"
include "adantr.mm"
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
include "cvv.mm"
include "cico.mm"
include "reex.mm"
include "abscld.mm"
include "absge0d.mm"
include "elrege0.mm"
include "0e0icopnf.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "eqidd.mm"
include "offval2.mm"
include "ovif2.mm"
include "absmuld.mm"
include "ifeq1da.mm"
include "recnd.mm"
include "mul01d.mm"
include "ifeq2d.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "iblabs.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "abscl.mm"
include "absge0.mm"
include "itg2mulc.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "cofr.mm"
include "releabsd.mm"
include "c1.mm"
include "absdivd.mm"
include "cn0.mm"
include "elfznn0.mm"
include "absexp.mm"
include "absi.mm"
include "oveq1i.mm"
include "1exp.mm"
include "oveq2d.mm"
include "div1d.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "breq1.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "adantl.mm"
include "3brtr4d.mm"
include "ex.mm"
include "0le0.mm"
include "iffalse.mm"
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

theorem iblmulc2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume itgmulc2.1: |- ( ph -> C e. CC )
  assume itgmulc2.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgmulc2.3: |- ( ph -> ( x e. A |-> B ) e. L^1 )

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
    wph
    vx
    cA
    cB
    cC
    cV
    itgmulc2.1
    itgmulc2.2
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @14
    cmbf
    wcel
    itgmulc2.3
    @14
    iblmbf
    syl
    #
    mbfmulc2
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
    @0
    cabs
    cfv
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
    @23
    cle
    wbr
    #
    @12
    @17
    vx
    cr
    @9
    @18
    @10
    @17
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
    @18
    @3
    @8
    @7
    cc0
    ifan
    #
    @17
    @28
    @18
    wcel
    @26
    @17
    @3
    @27
    cc0
    @18
    @17
    @3
    wa
    #
    @27
    cxr
    wcel
    cc0
    @27
    cle
    wbr
    #
    @27
    @18
    wcel
    @30
    @27
    @30
    @7
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @27
    cr
    wcel
    @30
    @6
    @30
    @0
    @5
    wph
    @3
    @0
    cc
    wcel
    @16
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
    #
    @3
    itgmulc2.1
    adantr
    #
    wph
    vx
    cA
    cB
    cV
    @15
    itgmulc2.2
    mbfmptcl
    #
    mulcld
    #
    adantlr
    #
    @30
    @4
    cz
    wcel
    #
    @5
    cc
    wcel
    #
    @16
    @40
    wph
    @3
    @4
    cc0
    c3
    elfzelz
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
    @40
    @41
    ax-icn
    ine0
    ci
    @4
    expclz
    mp3an12
    syl
    #
    @30
    @40
    @5
    cc0
    wne
    #
    @42
    @43
    @44
    @40
    @46
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
    @30
    @33
    @32
    @31
    0re
    @49
    cc0
    @7
    max1
    sylancr
    @27
    elxrge0
    sylanbrc
    cc0
    @18
    wcel
    #
    @17
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
    @24
    @16
    wph
    @23
    cC
    cabs
    cfv
    #
    vx
    cr
    @3
    cB
    cabs
    cfv
    #
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
    cr
    wph
    cr
    @54
    csn
    cxp
    #
    @57
    cmul
    cof
    co
    #
    citg2
    cfv
    @23
    @59
    wph
    @61
    @22
    citg2
    wph
    @61
    vx
    cr
    @54
    @56
    cmul
    co
    #
    cmpt
    @22
    wph
    vx
    cr
    @54
    @56
    cmul
    @60
    @57
    cvv
    cr
    cc0
    cpnf
    cico
    co
    #
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    wph
    @54
    cr
    wcel
    #
    @26
    wph
    cC
    itgmulc2.1
    abscld
    #
    adantr
    wph
    @56
    @63
    wcel
    @26
    wph
    @3
    @55
    cc0
    @63
    @34
    @55
    cr
    wcel
    cc0
    @55
    cle
    wbr
    @55
    @63
    wcel
    @34
    cB
    @37
    abscld
    #
    @34
    cB
    @37
    absge0d
    #
    @55
    elrege0
    sylanbrc
    cc0
    @63
    wcel
    wph
    @51
    wa
    #
    0e0icopnf
    a1i
    ifclda
    adantr
    #
    @60
    vx
    cr
    @54
    cmpt
    wceq
    wph
    vx
    cr
    @54
    fconstmpt
    a1i
    wph
    @57
    eqidd
    offval2
    wph
    vx
    cr
    @62
    @21
    wph
    @62
    @3
    @54
    @55
    cmul
    co
    #
    @54
    cc0
    cmul
    co
    #
    cif
    #
    @21
    @3
    @54
    @55
    cc0
    cmul
    ovif2
    wph
    @3
    @20
    @72
    cif
    @73
    @21
    wph
    @3
    @20
    @71
    @72
    @34
    cC
    cB
    @36
    @37
    absmuld
    ifeq1da
    wph
    @3
    @72
    cc0
    @20
    wph
    @54
    wph
    @54
    @66
    recnd
    mul01d
    ifeq2d
    eqtr3d
    syl5eq
    mpteq2dv
    eqtrd
    fveq2d
    wph
    @54
    @57
    wph
    vx
    cr
    @56
    @63
    @57
    @70
    @57
    eqid
    fmptd
    wph
    vx
    cA
    @55
    cmpt
    #
    cmbf
    wcel
    #
    @58
    cr
    wcel
    #
    wph
    @74
    cibl
    wcel
    @75
    @76
    wa
    wph
    vx
    cA
    cB
    cV
    itgmulc2.2
    itgmulc2.3
    iblabs
    wph
    vx
    cA
    @55
    @67
    @68
    iblpos
    mpbid
    simprd
    #
    wph
    @35
    @54
    @63
    wcel
    #
    itgmulc2.1
    @35
    @65
    cc0
    @54
    cle
    wbr
    @78
    cC
    abscl
    cC
    absge0
    @54
    elrege0
    sylanbrc
    syl
    itg2mulc
    eqtr3d
    wph
    @54
    @58
    @66
    @77
    remulcld
    eqeltrd
    adantr
    @17
    @19
    cr
    @18
    @22
    wf
    #
    @10
    @22
    cle
    cofr
    wbr
    #
    @25
    @53
    wph
    @79
    @16
    wph
    vx
    cr
    @21
    @18
    @22
    wph
    @21
    @18
    wcel
    #
    @26
    wph
    @3
    @20
    cc0
    @18
    @34
    @20
    cxr
    wcel
    cc0
    @20
    cle
    wbr
    #
    @20
    @18
    wcel
    @34
    @20
    @34
    @0
    @38
    abscld
    #
    rexrd
    @34
    @0
    @38
    absge0d
    #
    @20
    elxrge0
    sylanbrc
    @50
    @69
    0e0iccpnf
    a1i
    ifclda
    adantr
    #
    @22
    eqid
    fmptd
    adantr
    @17
    @80
    @9
    @21
    cle
    wbr
    #
    vx
    cr
    wral
    @17
    @86
    vx
    cr
    @17
    @9
    @28
    @21
    cle
    @29
    @17
    @3
    @28
    @21
    cle
    wbr
    #
    @17
    @3
    @87
    @30
    @27
    @20
    @28
    @21
    cle
    @30
    @7
    @20
    cle
    wbr
    #
    @82
    @27
    @20
    cle
    wbr
    #
    @30
    @7
    @6
    cabs
    cfv
    #
    @20
    cle
    @30
    @6
    @48
    releabsd
    @30
    @90
    @20
    @5
    cabs
    cfv
    #
    cdiv
    co
    @20
    c1
    cdiv
    co
    @20
    @30
    @0
    @5
    @39
    @45
    @47
    absdivd
    @30
    @91
    c1
    @20
    cdiv
    @30
    @91
    ci
    cabs
    cfv
    #
    @4
    cexp
    co
    #
    c1
    @30
    @43
    @4
    cn0
    wcel
    #
    @91
    @93
    wceq
    ax-icn
    @16
    @94
    wph
    @3
    @4
    c3
    elfznn0
    ad2antlr
    ci
    @4
    absexp
    sylancr
    @30
    @93
    c1
    @4
    cexp
    co
    #
    c1
    @92
    c1
    @4
    cexp
    absi
    oveq1i
    @30
    @40
    @95
    c1
    wceq
    @42
    @4
    1exp
    syl
    syl5eq
    eqtrd
    oveq2d
    @30
    @20
    wph
    @3
    @20
    cc
    wcel
    @16
    @34
    @20
    @83
    recnd
    adantlr
    div1d
    3eqtrd
    breqtrd
    wph
    @3
    @82
    @16
    @84
    adantlr
    @8
    @88
    @82
    @89
    @7
    cc0
    @7
    @27
    @20
    cle
    breq1
    cc0
    @27
    @20
    cle
    breq1
    ifboth
    syl2anc
    @3
    @28
    @27
    wceq
    @17
    @3
    @27
    cc0
    iftrue
    adantl
    @3
    @21
    @20
    wceq
    @17
    @3
    @20
    cc0
    iftrue
    adantl
    3brtr4d
    ex
    @51
    cc0
    cc0
    @28
    @21
    cle
    cc0
    cc0
    cle
    wbr
    @51
    0le0
    a1i
    @3
    @27
    cc0
    iffalse
    @3
    @20
    cc0
    iffalse
    3brtr4d
    pm2.61d1
    syl5eqbr
    ralrimivw
    @17
    vx
    cr
    @9
    @21
    cle
    @10
    @22
    cvv
    @18
    @18
    @64
    @17
    reex
    a1i
    @52
    wph
    @26
    @81
    @16
    @85
    adantlr
    @17
    @10
    eqidd
    @17
    @22
    eqidd
    ofrfval2
    mpbird
    @10
    @22
    itg2le
    syl3anc
    @23
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
    @34
    @7
    eqidd
    @38
    isibl2
    mpbir2and
end
