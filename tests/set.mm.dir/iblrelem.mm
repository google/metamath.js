include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "cneg.mm"
include "cim.mm"
include "w3a.mm"
include "eqid.mm"
include "iblcnlem.mm"
include "reim0d.mm"
include "itgvallem3.mm"
include "0re.mm"
include "syl6eqel.mm"
include "negeqd.mm"
include "neg0.mm"
include "syl6eq.mm"
include "jca.mm"
include "biantrud.mm"
include "rered.mm"
include "ibllem.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "bitr3d.mm"
include "anbi2d.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem iblrelem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> B ) e. MblFn /\ ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ B ) , B , 0 ) ) ) e. RR /\ ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u B ) , -u B , 0 ) ) ) e. RR ) ) )

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
    cre
    cfv
    #
    cle
    wbr
    wa
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
    wa
    #
    vx
    cr
    @2
    cc0
    cB
    cim
    cfv
    #
    cle
    wbr
    wa
    @14
    cc0
    cif
    cmpt
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
    @14
    cneg
    #
    cle
    wbr
    wa
    @17
    cc0
    cif
    cmpt
    citg2
    cfv
    #
    cr
    wcel
    #
    wa
    #
    w3a
    #
    @1
    vx
    cr
    @2
    cc0
    cB
    cle
    wbr
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
    wa
    @26
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
    wph
    vx
    cA
    cB
    @6
    @11
    @15
    @18
    cr
    @6
    eqid
    @11
    eqid
    @15
    eqid
    @18
    eqid
    iblrelem.1
    iblcnlem
    wph
    @1
    @13
    @20
    wa
    #
    wa
    @1
    @25
    @30
    wa
    #
    wa
    @21
    @31
    wph
    @32
    @33
    @1
    wph
    @13
    @32
    @33
    wph
    @20
    @13
    wph
    @16
    @19
    wph
    @15
    cc0
    cr
    wph
    vx
    cA
    @14
    wph
    @2
    wa
    #
    cB
    iblrelem.1
    reim0d
    #
    itgvallem3
    0re
    syl6eqel
    wph
    @18
    cc0
    cr
    wph
    vx
    cA
    @17
    @34
    @17
    cc0
    cneg
    cc0
    @34
    @14
    cc0
    @35
    negeqd
    neg0
    syl6eq
    itgvallem3
    0re
    syl6eqel
    jca
    biantrud
    wph
    @7
    @25
    @12
    @30
    wph
    @6
    @24
    cr
    wph
    @5
    @23
    citg2
    wph
    vx
    cr
    @4
    @22
    wph
    vx
    cA
    @3
    cB
    @34
    cB
    iblrelem.1
    rered
    #
    ibllem
    mpteq2dv
    fveq2d
    eleq1d
    wph
    @11
    @29
    cr
    wph
    @10
    @28
    citg2
    wph
    vx
    cr
    @9
    @27
    wph
    vx
    cA
    @8
    @26
    @34
    @3
    cB
    @36
    negeqd
    ibllem
    mpteq2dv
    fveq2d
    eleq1d
    anbi12d
    bitr3d
    anbi2d
    @1
    @13
    @20
    3anass
    @1
    @25
    @30
    3anass
    3bitr4g
    bitrd
end
