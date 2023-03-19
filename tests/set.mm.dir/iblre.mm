include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "cfv.mm"
include "cneg.mm"
include "w3a.mm"
include "cibl.mm"
include "mbfposb.mm"
include "wb.mm"
include "ifan.mm"
include "mpteq2i.mm"
include "fveq2i.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "a1i.mm"
include "anbi12d.mm"
include "3anass.mm"
include "an4.mm"
include "3bitr4g.mm"
include "iblrelem.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "sylancr.mm"
include "iblpos.mm"
include "renegcld.mm"
include "3bitr4d.mm"

theorem iblre
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> if ( 0 <_ B , B , 0 ) ) e. L^1 /\ ( x e. A |-> if ( 0 <_ -u B , -u B , 0 ) ) e. L^1 ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    cB
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
    cB
    cneg
    #
    cle
    wbr
    #
    wa
    @8
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
    w3a
    #
    vx
    cA
    @3
    cB
    cc0
    cif
    #
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cr
    @2
    @15
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
    wa
    #
    vx
    cA
    @9
    @8
    cc0
    cif
    #
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cr
    @2
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
    wa
    #
    wa
    #
    @0
    cibl
    wcel
    @16
    cibl
    wcel
    #
    @24
    cibl
    wcel
    #
    wa
    wph
    @1
    @7
    @13
    wa
    #
    wa
    @17
    @25
    wa
    #
    @21
    @29
    wa
    #
    wa
    @14
    @31
    wph
    @1
    @35
    @34
    @36
    wph
    vx
    cA
    cB
    iblrelem.1
    mbfposb
    @34
    @36
    wb
    wph
    @7
    @21
    @13
    @29
    @6
    @20
    cr
    @5
    @19
    citg2
    vx
    cr
    @4
    @18
    @2
    @3
    cB
    cc0
    ifan
    mpteq2i
    fveq2i
    eleq1i
    @12
    @28
    cr
    @11
    @27
    citg2
    vx
    cr
    @10
    @26
    @2
    @9
    @8
    cc0
    ifan
    mpteq2i
    fveq2i
    eleq1i
    anbi12i
    a1i
    anbi12d
    @1
    @7
    @13
    3anass
    @17
    @21
    @25
    @29
    an4
    3bitr4g
    wph
    vx
    cA
    cB
    iblrelem.1
    iblrelem
    wph
    @32
    @22
    @33
    @30
    wph
    vx
    cA
    @15
    wph
    @2
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @15
    cr
    wcel
    iblrelem.1
    0re
    @3
    cB
    cc0
    cr
    ifcl
    sylancl
    @37
    @39
    @38
    cc0
    @15
    cle
    wbr
    0re
    iblrelem.1
    cc0
    cB
    max1
    sylancr
    iblpos
    wph
    vx
    cA
    @23
    @37
    @8
    cr
    wcel
    #
    @39
    @23
    cr
    wcel
    @37
    cB
    iblrelem.1
    renegcld
    #
    0re
    @9
    @8
    cc0
    cr
    ifcl
    sylancl
    @37
    @39
    @40
    cc0
    @23
    cle
    wbr
    0re
    @41
    cc0
    @8
    max1
    sylancr
    iblpos
    anbi12d
    3bitr4d
end
