include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "wb.mm"
include "citg.mm"
include "wceq.mm"
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
include "mbfeqa.mm"
include "cpnf.mm"
include "cicc.mm"
include "ifan.mm"
include "cxr.mm"
include "cc.mm"
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
include "wss.mm"
include "covol.mm"
include "cdif.mm"
include "simpll.mm"
include "simpr.mm"
include "eldifn.mm"
include "eldifd.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "ibllem.mm"
include "cvv.mm"
include "eldifi.mm"
include "adantl.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt2.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "itg2eqa.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "anbi12d.mm"
include "eqidd.mm"
include "isibl2.mm"
include "3bitr4d.mm"
include "cmul.mm"
include "csu.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "dfitg.mm"
include "3eqtr4g.mm"
include "jca.mm"

theorem itgeqa
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  let vk: setvar k
  assume itgeqa.1: |- ( ( ph /\ x e. B ) -> C e. CC )
  assume itgeqa.2: |- ( ( ph /\ x e. B ) -> D e. CC )
  assume itgeqa.3: |- ( ph -> A C_ RR )
  assume itgeqa.4: |- ( ph -> ( vol* ` A ) = 0 )
  assume itgeqa.5: |- ( ( ph /\ x e. ( B \ A ) ) -> C = D )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B y
  disjoint C k
  disjoint C y
  disjoint D k
  disjoint D y
  disjoint k ph
  disjoint ph y
  assert |- ( ph -> ( ( ( x e. B |-> C ) e. L^1 <-> ( x e. B |-> D ) e. L^1 ) /\ S. B C _d x = S. B D _d x ) )

  proof
    wph
    vx
    cB
    cC
    cmpt
    #
    cibl
    wcel
    #
    vx
    cB
    cD
    cmpt
    #
    cibl
    wcel
    #
    wb
    vx
    cB
    cC
    citg
    #
    vx
    cB
    cD
    citg
    #
    wceq
    wph
    @0
    cmbf
    wcel
    #
    vx
    cr
    vx
    cv
    #
    cB
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
    #
    @12
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
    #
    wa
    @2
    cmbf
    wcel
    #
    vx
    cr
    @8
    cc0
    cD
    @10
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
    #
    @23
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
    @19
    wral
    #
    wa
    @1
    @3
    wph
    @6
    @21
    @20
    @30
    wph
    vx
    cA
    cB
    cC
    cD
    itgeqa.3
    itgeqa.4
    itgeqa.5
    itgeqa.1
    itgeqa.2
    mbfeqa
    wph
    @18
    @29
    vk
    @19
    wph
    @9
    @19
    wcel
    #
    wa
    #
    @17
    @28
    cr
    @32
    vy
    cA
    @16
    @27
    @32
    vx
    cr
    @15
    cc0
    cpnf
    cicc
    co
    #
    @16
    @32
    @15
    @33
    wcel
    @7
    cr
    wcel
    #
    @32
    @15
    @8
    @13
    @12
    cc0
    cif
    #
    cc0
    cif
    @33
    @8
    @13
    @12
    cc0
    ifan
    @32
    @8
    @35
    cc0
    @33
    @32
    @8
    wa
    #
    @35
    cxr
    wcel
    cc0
    @35
    cle
    wbr
    #
    @35
    @33
    wcel
    @36
    @35
    @36
    @12
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @35
    cr
    wcel
    @36
    @11
    @36
    cC
    @10
    wph
    @8
    cC
    cc
    wcel
    @31
    itgeqa.1
    adantlr
    @36
    @9
    cz
    wcel
    #
    @10
    cc
    wcel
    #
    @31
    @40
    wph
    @8
    @9
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
    @9
    expclz
    mp3an12
    syl
    #
    @36
    @40
    @10
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
    @9
    expne0i
    mp3an12
    syl
    #
    divcld
    recld
    #
    0re
    @13
    @12
    cc0
    cr
    ifcl
    sylancl
    rexrd
    @36
    @39
    @38
    @37
    0re
    @48
    cc0
    @12
    max1
    sylancr
    @35
    elxrge0
    sylanbrc
    cc0
    @33
    wcel
    @32
    @8
    wn
    wa
    0e0iccpnf
    a1i
    #
    ifclda
    syl5eqel
    adantr
    @16
    eqid
    #
    fmptd
    @32
    vx
    cr
    @26
    @33
    @27
    @32
    @26
    @33
    wcel
    @34
    @32
    @26
    @8
    @24
    @23
    cc0
    cif
    #
    cc0
    cif
    @33
    @8
    @24
    @23
    cc0
    ifan
    @32
    @8
    @51
    cc0
    @33
    @36
    @51
    cxr
    wcel
    cc0
    @51
    cle
    wbr
    #
    @51
    @33
    wcel
    @36
    @51
    @36
    @23
    cr
    wcel
    #
    @39
    @51
    cr
    wcel
    @36
    @22
    @36
    cD
    @10
    wph
    @8
    cD
    cc
    wcel
    @31
    itgeqa.2
    adantlr
    @45
    @47
    divcld
    recld
    #
    0re
    @24
    @23
    cc0
    cr
    ifcl
    sylancl
    rexrd
    @36
    @39
    @53
    @52
    0re
    @54
    cc0
    @23
    max1
    sylancr
    @51
    elxrge0
    sylanbrc
    @49
    ifclda
    syl5eqel
    adantr
    @27
    eqid
    #
    fmptd
    wph
    cA
    cr
    wss
    @31
    itgeqa.3
    adantr
    wph
    cA
    covol
    cfv
    cc0
    wceq
    @31
    itgeqa.4
    adantr
    wph
    vy
    cv
    #
    cr
    cA
    cdif
    #
    wcel
    @56
    @16
    cfv
    #
    @56
    @27
    cfv
    #
    wceq
    #
    @31
    wph
    @60
    vy
    @57
    wph
    @7
    @16
    cfv
    #
    @7
    @27
    cfv
    #
    wceq
    #
    vx
    @57
    wral
    @60
    vy
    @57
    wral
    wph
    @63
    vx
    @57
    wph
    @7
    @57
    wcel
    #
    wa
    #
    @15
    @26
    @61
    @62
    @65
    vx
    cB
    @12
    @23
    @65
    @8
    wa
    #
    @11
    @22
    cre
    @66
    cC
    cD
    @10
    cdiv
    @66
    wph
    @7
    cB
    cA
    cdif
    wcel
    cC
    cD
    wceq
    wph
    @64
    @8
    simpll
    @66
    @7
    cB
    cA
    @65
    @8
    simpr
    @64
    @7
    cA
    wcel
    wn
    wph
    @8
    @7
    cr
    cA
    eldifn
    ad2antlr
    eldifd
    itgeqa.5
    syl2anc
    oveq1d
    fveq2d
    ibllem
    @65
    @34
    @15
    cvv
    wcel
    @61
    @15
    wceq
    @64
    @34
    wph
    @7
    cr
    cA
    eldifi
    adantl
    #
    @14
    @12
    cc0
    @11
    cre
    fvex
    c0ex
    ifex
    vx
    cr
    @15
    cvv
    @16
    @50
    fvmpt2
    sylancl
    @65
    @34
    @26
    cvv
    wcel
    @62
    @26
    wceq
    @67
    @25
    @23
    cc0
    @22
    cre
    fvex
    c0ex
    ifex
    vx
    cr
    @26
    cvv
    @27
    @55
    fvmpt2
    sylancl
    3eqtr4d
    ralrimiva
    @63
    @60
    vx
    vy
    @57
    @63
    vy
    nfv
    vx
    @58
    @59
    vx
    cr
    @15
    @56
    nffvmpt1
    vx
    cr
    @26
    @56
    nffvmpt1
    nfeq
    @7
    @56
    wceq
    @61
    @58
    @62
    @59
    @7
    @56
    @16
    fveq2
    @7
    @56
    @27
    fveq2
    eqeq12d
    cbvral
    sylib
    r19.21bi
    adantlr
    itg2eqa
    #
    eleq1d
    ralbidva
    anbi12d
    wph
    vx
    cB
    cC
    @12
    vk
    @16
    cc
    wph
    @16
    eqidd
    wph
    @8
    wa
    #
    @12
    eqidd
    itgeqa.1
    isibl2
    wph
    vx
    cB
    cD
    @23
    vk
    @27
    cc
    wph
    @27
    eqidd
    @69
    @23
    eqidd
    itgeqa.2
    isibl2
    3bitr4d
    wph
    @19
    @10
    @17
    cmul
    co
    #
    vk
    csu
    @19
    @10
    @28
    cmul
    co
    #
    vk
    csu
    @4
    @5
    wph
    @19
    @70
    @71
    vk
    @32
    @17
    @28
    @10
    cmul
    @68
    oveq2d
    sumeq2dv
    vx
    cB
    cC
    @12
    vk
    @12
    eqid
    dfitg
    vx
    cB
    cD
    @23
    vk
    @23
    eqid
    dfitg
    3eqtr4g
    jca
end
