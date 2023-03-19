include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
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
include "iblrelem.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "iblposlem.mm"
include "0re.mm"
include "syl6eqel.mm"
include "biantrud.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "ancom.mm"
include "syl6rbb.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "3bitr2d.mm"

theorem iblpos
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume iblpos.2: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> B ) e. MblFn /\ ( S.2 ` ( x e. RR |-> if ( x e. A , B , 0 ) ) ) e. RR ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    #
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
    cle
    wbr
    #
    wa
    #
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
    wa
    #
    vx
    cr
    @3
    cc0
    cB
    cneg
    #
    cle
    wbr
    wa
    @11
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
    @10
    @2
    vx
    cr
    @3
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
    wa
    wph
    @1
    @2
    @9
    @13
    w3a
    @14
    wph
    vx
    cA
    cB
    iblrelem.1
    iblrelem
    @2
    @9
    @13
    df-3an
    syl6bb
    wph
    @13
    @10
    wph
    @12
    cc0
    cr
    wph
    vx
    cA
    cB
    iblrelem.1
    iblpos.2
    iblposlem
    0re
    syl6eqel
    biantrud
    wph
    @9
    @18
    @2
    wph
    @8
    @17
    cr
    wph
    @7
    @16
    citg2
    wph
    vx
    cr
    @6
    @15
    wph
    @5
    @3
    cB
    cc0
    wph
    @3
    @4
    @3
    wa
    @5
    wph
    @3
    @4
    wph
    @3
    @4
    iblpos.2
    ex
    pm4.71rd
    @4
    @3
    ancom
    syl6rbb
    ifbid
    mpteq2dv
    fveq2d
    eleq1d
    anbi2d
    3bitr2d
end
