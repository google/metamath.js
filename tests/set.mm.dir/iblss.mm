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
include "cres.mm"
include "resmptd.mm"
include "cvol.mm"
include "cdm.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfres.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "ifan.mm"
include "simpll.mm"
include "sselda.mm"
include "sylan.mm"
include "cxr.mm"
include "cc.mm"
include "mbfmptcl.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad3antlr.mm"
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
include "syldan.mm"
include "wn.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "fmptd.mm"
include "eqidd.mm"
include "iblitg.mm"
include "sylan2.mm"
include "cofr.mm"
include "leidd.mm"
include "breq1.mm"
include "ifboth.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "0le0.mm"
include "stoic1a.mm"
include "iffalse.mm"
include "3brtr4d.mm"
include "pm2.61dan.mm"
include "3brtr4g.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "reex.mm"
include "ofrfval2.mm"
include "mpbird.mm"
include "itg2le.mm"
include "syl3anc.mm"
include "itg2lecl.mm"
include "isibl2.mm"
include "mpbir2and.mm"

theorem iblss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume iblss.1: |- ( ph -> A C_ B )
  assume iblss.2: |- ( ph -> A e. dom vol )
  assume iblss.3: |- ( ( ph /\ x e. B ) -> C e. V )
  assume iblss.4: |- ( ph -> ( x e. B |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> ( x e. A |-> C ) e. L^1 )

  proof
    wph
    vx
    cA
    cC
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
    cC
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
    wph
    vx
    cB
    cC
    cmpt
    #
    cA
    cres
    #
    @0
    cmbf
    wph
    vx
    cB
    cA
    cC
    iblss.1
    resmptd
    wph
    @13
    cmbf
    wcel
    #
    cA
    cvol
    cdm
    wcel
    @14
    cmbf
    wcel
    wph
    @13
    cibl
    wcel
    @15
    iblss.4
    @13
    iblmbf
    syl
    #
    iblss.2
    cA
    @13
    mbfres
    syl2anc
    eqeltrrd
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
    @1
    cB
    wcel
    #
    @7
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
    @10
    @24
    cle
    wbr
    #
    @11
    @18
    vx
    cr
    @8
    @19
    @9
    @18
    @1
    cr
    wcel
    #
    wa
    #
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
    @19
    @2
    @7
    @6
    cc0
    ifan
    #
    @28
    @2
    @29
    cc0
    @19
    @28
    @2
    @21
    @29
    @19
    wcel
    #
    @28
    wph
    @2
    @21
    wph
    @17
    @27
    simpll
    #
    wph
    cA
    cB
    @1
    iblss.1
    sselda
    #
    sylan
    #
    @28
    @21
    wa
    #
    @29
    cxr
    wcel
    cc0
    @29
    cle
    wbr
    #
    @32
    @36
    @29
    @36
    @6
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @29
    cr
    wcel
    @36
    @5
    @36
    cC
    @4
    @28
    wph
    @21
    cC
    cc
    wcel
    #
    @33
    wph
    vx
    cB
    cC
    cV
    @16
    iblss.3
    mbfmptcl
    #
    sylan
    @36
    @3
    cz
    wcel
    #
    @4
    cc
    wcel
    #
    @17
    @42
    wph
    @27
    @21
    @3
    cc0
    c3
    elfzelz
    #
    ad3antlr
    #
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @42
    @43
    ax-icn
    ine0
    ci
    @3
    expclz
    mp3an12
    syl
    @36
    @42
    @4
    cc0
    wne
    #
    @45
    @46
    @47
    @42
    @48
    ax-icn
    ine0
    ci
    @3
    expne0i
    mp3an12
    syl
    divcld
    recld
    #
    0re
    @7
    @6
    cc0
    cr
    ifcl
    sylancl
    #
    rexrd
    @36
    @39
    @38
    @37
    0re
    @49
    cc0
    @6
    max1
    sylancr
    #
    @29
    elxrge0
    sylanbrc
    #
    syldan
    cc0
    @19
    wcel
    #
    @28
    @2
    wn
    #
    wa
    0e0iccpnf
    a1i
    ifclda
    syl5eqel
    #
    @9
    eqid
    fmptd
    #
    @17
    wph
    @42
    @25
    @44
    wph
    vx
    cB
    cC
    @6
    @23
    @3
    cV
    wph
    @23
    eqidd
    wph
    @21
    wa
    @6
    eqidd
    iblss.4
    iblss.3
    iblitg
    sylan2
    @18
    @20
    cr
    @19
    @23
    wf
    @9
    @23
    cle
    cofr
    wbr
    #
    @26
    @56
    @18
    vx
    cr
    @22
    @19
    @23
    @28
    @22
    @21
    @29
    cc0
    cif
    #
    @19
    @21
    @7
    @6
    cc0
    ifan
    #
    @28
    @21
    @29
    cc0
    @19
    @52
    @53
    @28
    @21
    wn
    #
    wa
    #
    0e0iccpnf
    a1i
    ifclda
    syl5eqel
    #
    @23
    eqid
    fmptd
    @18
    @57
    @8
    @22
    cle
    wbr
    #
    vx
    cr
    wral
    @18
    @63
    vx
    cr
    @28
    @30
    @58
    @8
    @22
    cle
    @28
    @21
    @30
    @58
    cle
    wbr
    @36
    @30
    @29
    @58
    cle
    @36
    @29
    @29
    cle
    wbr
    #
    @37
    @30
    @29
    cle
    wbr
    #
    @36
    @29
    @50
    leidd
    @51
    @2
    @64
    @37
    @65
    @29
    cc0
    @29
    @30
    @29
    cle
    breq1
    cc0
    @30
    @29
    cle
    breq1
    ifboth
    syl2anc
    @21
    @58
    @29
    wceq
    @28
    @21
    @29
    cc0
    iftrue
    adantl
    breqtrrd
    @61
    cc0
    cc0
    @30
    @58
    cle
    cc0
    cc0
    cle
    wbr
    @61
    0le0
    a1i
    @61
    @54
    @30
    cc0
    wceq
    @28
    @2
    @21
    @35
    stoic1a
    @2
    @29
    cc0
    iffalse
    syl
    @60
    @58
    cc0
    wceq
    @28
    @21
    @29
    cc0
    iffalse
    adantl
    3brtr4d
    pm2.61dan
    @31
    @59
    3brtr4g
    ralrimiva
    @18
    vx
    cr
    @8
    @22
    cle
    @9
    @23
    cvv
    @19
    @19
    cr
    cvv
    wcel
    @18
    reex
    a1i
    @55
    @62
    @18
    @9
    eqidd
    @18
    @23
    eqidd
    ofrfval2
    mpbird
    @9
    @23
    itg2le
    syl3anc
    @24
    @9
    itg2lecl
    syl3anc
    ralrimiva
    wph
    vx
    cA
    cC
    @6
    vk
    @9
    cc
    wph
    @9
    eqidd
    wph
    @2
    wa
    @6
    eqidd
    wph
    @2
    @21
    @40
    @34
    @41
    syldan
    isibl2
    mpbir2and
end
