include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cibl.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
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
include "cmpt.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "cc.mm"
include "0cn.mm"
include "mbfconst.mm"
include "mpan2.mm"
include "cz.mm"
include "wceq.mm"
include "elfzelz.mm"
include "ad2antlr.mm"
include "wne.mm"
include "ax-icn.mm"
include "ine0.mm"
include "w3a.mm"
include "expclz.mm"
include "expne0i.mm"
include "div0d.mm"
include "mp3an12.mm"
include "syl.mm"
include "fveq2d.mm"
include "re0.mm"
include "syl6eq.mm"
include "itgvallem3.mm"
include "0re.mm"
include "syl6eqel.mm"
include "ralrimiva.mm"
include "eqidd.mm"
include "wf.mm"
include "c0ex.mm"
include "fconst.mm"
include "fdm.mm"
include "mp1i.mm"
include "fvconst2.mm"
include "adantl.mm"
include "isibl.mm"
include "mpbir2and.mm"

theorem ibl0
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. dom vol -> ( A X. { 0 } ) e. L^1 )

  proof
    cA
    cvol
    cdm
    wcel
    #
    cA
    cc0
    csn
    #
    cxp
    #
    cibl
    wcel
    @2
    cmbf
    wcel
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    cc0
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
    wa
    @9
    cc0
    cif
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
    @0
    cc0
    cc
    wcel
    @3
    0cn
    cA
    cc0
    mbfconst
    mpan2
    @0
    @12
    vk
    @13
    @0
    @6
    @13
    wcel
    #
    wa
    #
    @11
    cc0
    cr
    @15
    vx
    cA
    @9
    @15
    @5
    wa
    #
    @9
    cc0
    cre
    cfv
    cc0
    @16
    @8
    cc0
    cre
    @16
    @6
    cz
    wcel
    #
    @8
    cc0
    wceq
    #
    @14
    @17
    @0
    @5
    @6
    cc0
    c3
    elfzelz
    ad2antlr
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @17
    @18
    ax-icn
    ine0
    @19
    @20
    @17
    w3a
    @7
    ci
    @6
    expclz
    ci
    @6
    expne0i
    div0d
    mp3an12
    syl
    fveq2d
    re0
    syl6eq
    itgvallem3
    0re
    syl6eqel
    ralrimiva
    @0
    vx
    cA
    cc0
    @9
    vk
    @2
    @10
    @0
    @10
    eqidd
    @0
    @5
    wa
    @9
    eqidd
    cA
    @1
    @2
    wf
    @2
    cdm
    cA
    wceq
    @0
    cA
    cc0
    c0ex
    fconst
    cA
    @1
    @2
    fdm
    mp1i
    @5
    @4
    @2
    cfv
    cc0
    wceq
    @0
    cA
    cc0
    @4
    c0ex
    fvconst2
    adantl
    isibl
    mpbir2and
end
