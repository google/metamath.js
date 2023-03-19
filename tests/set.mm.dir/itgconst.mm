include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "cc.mm"
include "w3a.mm"
include "cre.mm"
include "citg.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "recl.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cneg.mm"
include "cmin.mm"
include "simplr.mm"
include "csn.mm"
include "cxp.mm"
include "cibl.mm"
include "fconstmpt.mm"
include "simpl1.mm"
include "simp2.mm"
include "adantr.mm"
include "simpr.mm"
include "recnd.mm"
include "iblconst.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"
include "itgrevallem1.mm"
include "ifan.mm"
include "mpteq2i.mm"
include "fveq2i.mm"
include "cpnf.mm"
include "cico.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "sylancr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "itg2const.mm"
include "syl5eq.mm"
include "renegcl.mm"
include "adantl.mm"
include "oveq12d.mm"
include "subdird.mm"
include "max0sub.mm"
include "oveq1d.mm"
include "3eqtr2rd.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "simpl.mm"
include "itgeq2dv.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "imcl.mm"
include "oveq2d.mm"
include "ax-icn.mm"
include "a1i.mm"
include "mulassd.mm"
include "mulcl.mm"
include "adddird.mm"
include "simpl3.mm"
include "itgcnval.mm"
include "replim.mm"
include "3eqtr4d.mm"

theorem itgconst
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A y
  disjoint B k
  disjoint B y
  assert |- ( ( A e. dom vol /\ ( vol ` A ) e. RR /\ B e. CC ) -> S. A B _d x = ( B x. ( vol ` A ) ) )

  proof
    cA
    cvol
    cdm
    wcel
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    cB
    cc
    wcel
    #
    w3a
    #
    vx
    cA
    cB
    cre
    cfv
    #
    citg
    #
    ci
    vx
    cA
    cB
    cim
    cfv
    #
    citg
    #
    cmul
    co
    #
    caddc
    co
    #
    @5
    ci
    @7
    cmul
    co
    #
    caddc
    co
    #
    @1
    cmul
    co
    #
    vx
    cA
    cB
    citg
    cB
    @1
    cmul
    co
    @4
    @10
    @5
    @1
    cmul
    co
    #
    @11
    @1
    cmul
    co
    #
    caddc
    co
    @13
    @4
    @6
    @14
    @9
    @15
    caddc
    @4
    @5
    cr
    wcel
    #
    vx
    cA
    vy
    cv
    #
    citg
    #
    @17
    @1
    cmul
    co
    #
    wceq
    #
    vy
    cr
    wral
    #
    @6
    @14
    wceq
    #
    @3
    @0
    @16
    @2
    cB
    recl
    3ad2ant3
    #
    @4
    @20
    vy
    cr
    @4
    @17
    cr
    wcel
    #
    wa
    #
    @18
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    @17
    cle
    wbr
    #
    wa
    @17
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
    @26
    cc0
    @17
    cneg
    #
    cle
    wbr
    #
    wa
    @31
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmin
    co
    #
    @19
    @25
    vx
    cA
    @17
    @4
    @24
    @26
    simplr
    @25
    vx
    cA
    @17
    cmpt
    cA
    @17
    csn
    cxp
    #
    cibl
    vx
    cA
    @17
    fconstmpt
    @25
    @0
    @2
    @17
    cc
    wcel
    @37
    cibl
    wcel
    @0
    @2
    @3
    @24
    simpl1
    #
    @4
    @2
    @24
    @0
    @2
    @3
    simp2
    #
    adantr
    #
    @25
    @17
    @4
    @24
    simpr
    #
    recnd
    cA
    @17
    iblconst
    syl3anc
    syl5eqelr
    itgrevallem1
    @25
    @36
    @27
    @17
    cc0
    cif
    #
    @1
    cmul
    co
    #
    @32
    @31
    cc0
    cif
    #
    @1
    cmul
    co
    #
    cmin
    co
    @42
    @44
    cmin
    co
    #
    @1
    cmul
    co
    @19
    @25
    @30
    @43
    @35
    @45
    cmin
    @25
    @30
    vx
    cr
    @26
    @42
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @43
    @29
    @48
    citg2
    vx
    cr
    @28
    @47
    @26
    @27
    @17
    cc0
    ifan
    mpteq2i
    fveq2i
    @25
    @0
    @2
    @42
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @49
    @43
    wceq
    @38
    @40
    @25
    @42
    cr
    wcel
    #
    cc0
    @42
    cle
    wbr
    #
    @51
    @25
    @24
    cc0
    cr
    wcel
    #
    @52
    @41
    0re
    @27
    @17
    cc0
    cr
    ifcl
    sylancl
    #
    @25
    @54
    @24
    @53
    0re
    @41
    cc0
    @17
    max1
    sylancr
    @42
    elrege0
    sylanbrc
    vx
    cA
    @42
    itg2const
    syl3anc
    syl5eq
    @25
    @35
    vx
    cr
    @26
    @44
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @45
    @34
    @57
    citg2
    vx
    cr
    @33
    @56
    @26
    @32
    @31
    cc0
    ifan
    mpteq2i
    fveq2i
    @25
    @0
    @2
    @44
    @50
    wcel
    #
    @58
    @45
    wceq
    @38
    @40
    @25
    @44
    cr
    wcel
    #
    cc0
    @44
    cle
    wbr
    #
    @59
    @25
    @31
    cr
    wcel
    #
    @54
    @60
    @24
    @62
    @4
    @17
    renegcl
    adantl
    #
    0re
    @32
    @31
    cc0
    cr
    ifcl
    sylancl
    #
    @25
    @54
    @62
    @61
    0re
    @63
    cc0
    @31
    max1
    sylancr
    @44
    elrege0
    sylanbrc
    vx
    cA
    @44
    itg2const
    syl3anc
    syl5eq
    oveq12d
    @25
    @42
    @44
    @1
    @25
    @42
    @55
    recnd
    @25
    @44
    @64
    recnd
    @4
    @1
    cc
    wcel
    @24
    @4
    @1
    @39
    recnd
    #
    adantr
    subdird
    @25
    @46
    @17
    @1
    cmul
    @24
    @46
    @17
    wceq
    @4
    @17
    max0sub
    adantl
    oveq1d
    3eqtr2rd
    eqtr4d
    ralrimiva
    #
    @20
    @22
    vy
    @5
    cr
    @17
    @5
    wceq
    #
    @18
    @6
    @19
    @14
    @67
    vx
    cA
    @17
    @5
    @67
    @26
    simpl
    itgeq2dv
    @17
    @5
    @1
    cmul
    oveq1
    eqeq12d
    rspcv
    sylc
    @4
    @9
    ci
    @7
    @1
    cmul
    co
    #
    cmul
    co
    @15
    @4
    @8
    @68
    ci
    cmul
    @4
    @7
    cr
    wcel
    #
    @21
    @8
    @68
    wceq
    #
    @3
    @0
    @69
    @2
    cB
    imcl
    3ad2ant3
    #
    @66
    @20
    @70
    vy
    @7
    cr
    @17
    @7
    wceq
    #
    @18
    @8
    @19
    @68
    @72
    vx
    cA
    @17
    @7
    @72
    @26
    simpl
    itgeq2dv
    @17
    @7
    @1
    cmul
    oveq1
    eqeq12d
    rspcv
    sylc
    oveq2d
    @4
    ci
    @7
    @1
    ci
    cc
    wcel
    #
    @4
    ax-icn
    a1i
    @4
    @7
    @71
    recnd
    #
    @65
    mulassd
    eqtr4d
    oveq12d
    @4
    @5
    @11
    @1
    @4
    @5
    @23
    recnd
    @4
    @73
    @7
    cc
    wcel
    @11
    cc
    wcel
    ax-icn
    @74
    ci
    @7
    mulcl
    sylancr
    @65
    adddird
    eqtr4d
    @4
    vx
    cA
    cB
    cc
    @0
    @2
    @3
    @26
    simpl3
    @4
    vx
    cA
    cB
    cmpt
    cA
    cB
    csn
    cxp
    cibl
    vx
    cA
    cB
    fconstmpt
    cA
    cB
    iblconst
    syl5eqelr
    itgcnval
    @4
    cB
    @12
    @1
    cmul
    @3
    @0
    cB
    @12
    wceq
    @2
    cB
    replim
    3ad2ant3
    oveq1d
    3eqtr4d
end
