include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "cc.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cibl.mm"
include "fconstmpt.mm"
include "cmbf.mm"
include "cv.mm"
include "cc0.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "mbfconst.mm"
include "3adant2.mm"
include "syl5eqelr.mm"
include "cmul.mm"
include "ifan.mm"
include "mpteq2i.mm"
include "fveq2i.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
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
include "max1.mm"
include "sylancr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "itg2const.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "eqidd.mm"
include "isibl2.mm"
include "mpbir2and.mm"
include "syl5eqel.mm"

theorem iblconst
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. dom vol /\ ( vol ` A ) e. RR /\ B e. CC ) -> ( A X. { B } ) e. L^1 )

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
    cA
    cB
    csn
    cxp
    #
    vx
    cA
    cB
    cmpt
    #
    cibl
    vx
    cA
    cB
    fconstmpt
    #
    @4
    @6
    cibl
    wcel
    @6
    cmbf
    wcel
    vx
    cr
    vx
    cv
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
    @4
    @6
    @5
    cmbf
    @7
    @0
    @3
    @5
    cmbf
    wcel
    @2
    cA
    cB
    mbfconst
    3adant2
    syl5eqelr
    @4
    @17
    vk
    @18
    @4
    @9
    @18
    wcel
    #
    wa
    #
    @16
    @13
    @12
    cc0
    cif
    #
    @1
    cmul
    co
    #
    cr
    @20
    @16
    vx
    cr
    @8
    @21
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @22
    @15
    @24
    citg2
    vx
    cr
    @14
    @23
    @8
    @13
    @12
    cc0
    ifan
    mpteq2i
    fveq2i
    @20
    @0
    @2
    @21
    cc0
    cpnf
    cico
    co
    wcel
    #
    @25
    @22
    wceq
    @0
    @2
    @3
    @19
    simpl1
    @0
    @2
    @3
    @19
    simpl2
    #
    @20
    @21
    cr
    wcel
    #
    cc0
    @21
    cle
    wbr
    #
    @26
    @20
    @12
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @28
    @20
    @11
    @20
    cB
    @10
    @0
    @2
    @3
    @19
    simpl3
    @20
    @9
    cz
    wcel
    #
    @10
    cc
    wcel
    #
    @19
    @32
    @4
    @9
    cc0
    c3
    elfzelz
    adantl
    #
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @32
    @33
    ax-icn
    ine0
    ci
    @9
    expclz
    mp3an12
    syl
    @20
    @32
    @10
    cc0
    wne
    #
    @34
    @35
    @36
    @32
    @37
    ax-icn
    ine0
    ci
    @9
    expne0i
    mp3an12
    syl
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
    #
    @20
    @31
    @30
    @29
    0re
    @38
    cc0
    @12
    max1
    sylancr
    @21
    elrege0
    sylanbrc
    vx
    cA
    @21
    itg2const
    syl3anc
    syl5eq
    @20
    @21
    @1
    @39
    @27
    remulcld
    eqeltrd
    ralrimiva
    @4
    vx
    cA
    cB
    @12
    vk
    @15
    cc
    @4
    @15
    eqidd
    @4
    @8
    wa
    @12
    eqidd
    @0
    @2
    @3
    @8
    simpl3
    isibl2
    mpbir2and
    syl5eqel
end
