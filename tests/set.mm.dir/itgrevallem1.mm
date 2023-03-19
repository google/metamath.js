include "citg.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "caddc.mm"
include "eqid.mm"
include "itgcnlem.mm"
include "rered.mm"
include "ibllem.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "oveq12d.mm"
include "reim0d.mm"
include "itgvallem3.mm"
include "neg0.mm"
include "syl6eq.mm"
include "0m0e0.mm"
include "oveq2d.mm"
include "it0e0.mm"
include "cmbf.mm"
include "cibl.mm"
include "w3a.mm"
include "iblrelem.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simp3d.mm"
include "resubcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "3eqtrd.mm"

theorem itgrevallem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgreval.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> S. A B _d x = ( ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ B ) , B , 0 ) ) ) - ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u B ) , -u B , 0 ) ) ) ) )

  proof
    wph
    vx
    cA
    cB
    citg
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
    @1
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
    @0
    cc0
    @1
    cneg
    #
    cle
    wbr
    wa
    @5
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
    ci
    vx
    cr
    @0
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
    vx
    cr
    @0
    cc0
    @10
    cneg
    #
    cle
    wbr
    wa
    @12
    cc0
    cif
    cmpt
    citg2
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    vx
    cr
    @0
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
    vx
    cr
    @0
    cc0
    cB
    cneg
    #
    cle
    wbr
    wa
    @19
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
    cc0
    caddc
    co
    @23
    wph
    vx
    cA
    cB
    @4
    @8
    @11
    @13
    cr
    @4
    eqid
    @8
    eqid
    @11
    eqid
    @13
    eqid
    iblrelem.1
    itgreval.2
    itgcnlem
    wph
    @9
    @23
    @15
    cc0
    caddc
    wph
    @4
    @18
    @8
    @22
    cmin
    wph
    @3
    @17
    citg2
    wph
    vx
    cr
    @2
    @16
    wph
    vx
    cA
    @1
    cB
    wph
    @0
    wa
    #
    cB
    iblrelem.1
    rered
    #
    ibllem
    mpteq2dv
    fveq2d
    wph
    @7
    @21
    citg2
    wph
    vx
    cr
    @6
    @20
    wph
    vx
    cA
    @5
    @19
    @24
    @1
    cB
    @25
    negeqd
    ibllem
    mpteq2dv
    fveq2d
    oveq12d
    wph
    @15
    ci
    cc0
    cmul
    co
    cc0
    wph
    @14
    cc0
    ci
    cmul
    wph
    @14
    cc0
    cc0
    cmin
    co
    cc0
    wph
    @11
    cc0
    @13
    cc0
    cmin
    wph
    vx
    cA
    @10
    @24
    cB
    iblrelem.1
    reim0d
    #
    itgvallem3
    wph
    vx
    cA
    @12
    @24
    @12
    cc0
    cneg
    cc0
    @24
    @10
    cc0
    @26
    negeqd
    neg0
    syl6eq
    itgvallem3
    oveq12d
    0m0e0
    syl6eq
    oveq2d
    it0e0
    syl6eq
    oveq12d
    wph
    @23
    wph
    @23
    wph
    @18
    @22
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @18
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    wph
    @27
    cibl
    wcel
    @28
    @29
    @30
    w3a
    itgreval.2
    wph
    vx
    cA
    cB
    iblrelem.1
    iblrelem
    mpbid
    #
    simp2d
    wph
    @28
    @29
    @30
    @31
    simp3d
    resubcld
    recnd
    addid1d
    3eqtrd
end
