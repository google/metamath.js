include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
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
include "ifan.mm"
include "cxr.mm"
include "cc.mm"
include "mbfmptcl.mm"
include "adantlr.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad2antlr.mm"
include "wne.mm"
include "ax-icn.mm"
include "ine0.mm"
include "expclz.mm"
include "mp3an12.mm"
include "syl.mm"
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
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "abscld.mm"
include "absge0d.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "cofr.mm"
include "releabsd.mm"
include "c1.mm"
include "absdivd.mm"
include "cn0.mm"
include "wceq.mm"
include "elfznn0.mm"
include "absexp.mm"
include "absi.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "recnd.mm"
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
include "cvv.mm"
include "reex.mm"
include "eqidd.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"
include "ralrimiva.mm"
include "isibl2.mm"
include "mpbir2and.mm"

theorem iblabsr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  assume iblabsr.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume iblabsr.2: |- ( ph -> ( x e. A |-> B ) e. MblFn )
  assume iblabsr.3: |- ( ph -> ( x e. A |-> ( abs ` B ) ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> ( x e. A |-> B ) e. L^1 )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @0
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
    cB
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
    @6
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
    iblabsr.2
    wph
    @11
    vk
    @12
    wph
    @3
    @12
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
    @9
    wf
    #
    vx
    cr
    @2
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
    cr
    wcel
    #
    @10
    @20
    cle
    wbr
    #
    @11
    @14
    vx
    cr
    @8
    @15
    @9
    @14
    @8
    @15
    wcel
    @1
    cr
    wcel
    #
    @14
    @8
    @2
    @7
    @6
    cc0
    cif
    #
    cc0
    cif
    #
    @15
    @2
    @7
    @6
    cc0
    ifan
    #
    @14
    @2
    @24
    cc0
    @15
    @14
    @2
    wa
    #
    @24
    cxr
    wcel
    cc0
    @24
    cle
    wbr
    #
    @24
    @15
    wcel
    @27
    @24
    @27
    @6
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @24
    cr
    wcel
    @27
    @5
    @27
    cB
    @4
    wph
    @2
    cB
    cc
    wcel
    @13
    wph
    vx
    cA
    cB
    cV
    iblabsr.2
    iblabsr.1
    mbfmptcl
    #
    adantlr
    #
    @27
    @3
    cz
    wcel
    #
    @4
    cc
    wcel
    #
    @13
    @33
    wph
    @2
    @3
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
    @33
    @34
    ax-icn
    ine0
    ci
    @3
    expclz
    mp3an12
    syl
    #
    @27
    @33
    @4
    cc0
    wne
    #
    @35
    @36
    @37
    @33
    @39
    ax-icn
    ine0
    ci
    @3
    expne0i
    mp3an12
    syl
    #
    divcld
    #
    recld
    #
    0re
    @7
    @6
    cc0
    cr
    ifcl
    sylancl
    rexrd
    @27
    @30
    @29
    @28
    0re
    @42
    cc0
    @6
    max1
    sylancr
    @24
    elxrge0
    sylanbrc
    cc0
    @15
    wcel
    #
    @14
    @2
    wn
    #
    wa
    0e0iccpnf
    a1i
    #
    ifclda
    syl5eqel
    adantr
    #
    @9
    eqid
    fmptd
    #
    wph
    @21
    @13
    wph
    vx
    cA
    @17
    cmpt
    #
    cmbf
    wcel
    #
    @21
    wph
    @48
    cibl
    wcel
    @49
    @21
    wa
    iblabsr.3
    wph
    vx
    cA
    @17
    wph
    @2
    wa
    #
    cB
    @31
    abscld
    #
    @50
    cB
    @31
    absge0d
    #
    iblpos
    mpbid
    simprd
    adantr
    @14
    @16
    cr
    @15
    @19
    wf
    #
    @9
    @19
    cle
    cofr
    wbr
    #
    @22
    @47
    wph
    @53
    @13
    wph
    vx
    cr
    @18
    @15
    @19
    wph
    @18
    @15
    wcel
    #
    @23
    wph
    @2
    @17
    cc0
    @15
    @50
    @17
    cxr
    wcel
    #
    cc0
    @17
    cle
    wbr
    #
    @17
    @15
    wcel
    #
    @50
    @17
    @51
    rexrd
    #
    @52
    @17
    elxrge0
    #
    sylanbrc
    @43
    wph
    @44
    wa
    0e0iccpnf
    a1i
    ifclda
    adantr
    @19
    eqid
    fmptd
    adantr
    @14
    @54
    @8
    @18
    cle
    wbr
    #
    vx
    cr
    wral
    @14
    @61
    vx
    cr
    @14
    @8
    @25
    @18
    cle
    @26
    @14
    @2
    @25
    @18
    cle
    wbr
    #
    @14
    @2
    @62
    @27
    @24
    @17
    @25
    @18
    cle
    @27
    @6
    @17
    cle
    wbr
    #
    @57
    @24
    @17
    cle
    wbr
    #
    @27
    @6
    @5
    cabs
    cfv
    #
    @17
    cle
    @27
    @5
    @41
    releabsd
    @27
    @65
    @17
    @4
    cabs
    cfv
    #
    cdiv
    co
    @17
    c1
    cdiv
    co
    @17
    @27
    cB
    @4
    @32
    @38
    @40
    absdivd
    @27
    @66
    c1
    @17
    cdiv
    @27
    @66
    ci
    cabs
    cfv
    #
    @3
    cexp
    co
    #
    c1
    @27
    @36
    @3
    cn0
    wcel
    #
    @66
    @68
    wceq
    ax-icn
    @13
    @69
    wph
    @2
    @3
    c3
    elfznn0
    ad2antlr
    ci
    @3
    absexp
    sylancr
    @27
    @68
    c1
    @3
    cexp
    co
    #
    c1
    @67
    c1
    @3
    cexp
    absi
    oveq1i
    @27
    @33
    @70
    c1
    wceq
    @35
    @3
    1exp
    syl
    syl5eq
    eqtrd
    oveq2d
    @27
    @17
    wph
    @2
    @17
    cc
    wcel
    @13
    @50
    @17
    @51
    recnd
    adantlr
    div1d
    3eqtrd
    breqtrd
    @27
    cB
    @32
    absge0d
    #
    @7
    @63
    @57
    @64
    @6
    cc0
    @6
    @24
    @17
    cle
    breq1
    cc0
    @24
    @17
    cle
    breq1
    ifboth
    syl2anc
    @2
    @25
    @24
    wceq
    @14
    @2
    @24
    cc0
    iftrue
    adantl
    @2
    @18
    @17
    wceq
    @14
    @2
    @17
    cc0
    iftrue
    adantl
    3brtr4d
    ex
    @44
    cc0
    cc0
    @25
    @18
    cle
    cc0
    cc0
    cle
    wbr
    @44
    0le0
    a1i
    @2
    @24
    cc0
    iffalse
    @2
    @17
    cc0
    iffalse
    3brtr4d
    pm2.61d1
    syl5eqbr
    ralrimivw
    @14
    vx
    cr
    @8
    @18
    cle
    @9
    @19
    cvv
    @15
    @15
    cr
    cvv
    wcel
    @14
    reex
    a1i
    @46
    @14
    @55
    @23
    @14
    @2
    @17
    cc0
    @15
    @27
    @56
    @57
    @58
    wph
    @2
    @56
    @13
    @59
    adantlr
    @71
    @60
    sylanbrc
    @45
    ifclda
    adantr
    @14
    @9
    eqidd
    @14
    @19
    eqidd
    ofrfval2
    mpbird
    @9
    @19
    itg2le
    syl3anc
    @20
    @9
    itg2lecl
    syl3anc
    ralrimiva
    wph
    vx
    cA
    cB
    @6
    vk
    @9
    cV
    wph
    @9
    eqidd
    @50
    @6
    eqidd
    iblabsr.1
    isibl2
    mpbir2and
end
