include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
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
include "cibl.mm"
include "ismbfcn2.mm"
include "anbi1d.mm"
include "3anass.mm"
include "an4.mm"
include "3bitr4g.mm"
include "eqid.mm"
include "iblcnlem1.mm"
include "recld.mm"
include "iblrelem.mm"
include "syl6bb.mm"
include "imcld.mm"
include "anbi12d.mm"
include "3bitr4d.mm"

theorem iblcn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblcn.1: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> ( Re ` B ) ) e. L^1 /\ ( x e. A |-> ( Im ` B ) ) e. L^1 ) ) )

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
    cre
    cfv
    #
    cle
    wbr
    wa
    @3
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
    @3
    cneg
    #
    cle
    wbr
    wa
    @6
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
    @10
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
    @10
    cneg
    #
    cle
    wbr
    wa
    @13
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
    vx
    cA
    @3
    cmpt
    #
    cmbf
    wcel
    #
    @9
    wa
    #
    vx
    cA
    @10
    cmpt
    #
    cmbf
    wcel
    #
    @16
    wa
    #
    wa
    #
    @0
    cibl
    wcel
    @18
    cibl
    wcel
    #
    @21
    cibl
    wcel
    #
    wa
    wph
    @1
    @9
    @16
    wa
    #
    wa
    @19
    @22
    wa
    #
    @27
    wa
    @17
    @24
    wph
    @1
    @28
    @27
    wph
    vx
    cA
    cB
    iblcn.1
    ismbfcn2
    anbi1d
    @1
    @9
    @16
    3anass
    @19
    @9
    @22
    @16
    an4
    3bitr4g
    wph
    vx
    cA
    cB
    @4
    @7
    @11
    @14
    @4
    eqid
    @7
    eqid
    @11
    eqid
    @14
    eqid
    iblcn.1
    iblcnlem1
    wph
    @25
    @20
    @26
    @23
    wph
    @25
    @19
    @5
    @8
    w3a
    @20
    wph
    vx
    cA
    @3
    wph
    @2
    wa
    #
    cB
    iblcn.1
    recld
    iblrelem
    @19
    @5
    @8
    3anass
    syl6bb
    wph
    @26
    @22
    @12
    @15
    w3a
    @23
    wph
    vx
    cA
    @10
    @29
    cB
    iblcn.1
    imcld
    iblrelem
    @22
    @12
    @15
    3anass
    syl6bb
    anbi12d
    3bitr4d
end
