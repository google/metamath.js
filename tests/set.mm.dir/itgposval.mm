include "citg.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "itgrevallem1.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "ancom.mm"
include "syl6rbb.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "iblposlem.mm"
include "oveq12d.mm"
include "cmbf.mm"
include "cibl.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "recnd.mm"
include "subid1d.mm"
include "3eqtrd.mm"

theorem itgposval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgreval.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgposval.3: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> S. A B _d x = ( S.2 ` ( x e. RR |-> if ( x e. A , B , 0 ) ) ) )

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
    @6
    cc0
    cif
    cmpt
    citg2
    cfv
    #
    cmin
    co
    vx
    cr
    @0
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cc0
    cmin
    co
    @10
    wph
    vx
    cA
    cB
    iblrelem.1
    itgreval.2
    itgrevallem1
    wph
    @5
    @10
    @7
    cc0
    cmin
    wph
    @4
    @9
    citg2
    wph
    vx
    cr
    @3
    @8
    wph
    @2
    @0
    cB
    cc0
    wph
    @0
    @1
    @0
    wa
    @2
    wph
    @0
    @1
    wph
    @0
    @1
    itgposval.3
    ex
    pm4.71rd
    @1
    @0
    ancom
    syl6rbb
    ifbid
    mpteq2dv
    fveq2d
    wph
    vx
    cA
    cB
    iblrelem.1
    itgposval.3
    iblposlem
    oveq12d
    wph
    @10
    wph
    @10
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @10
    cr
    wcel
    #
    wph
    @11
    cibl
    wcel
    @12
    @13
    wa
    itgreval.2
    wph
    vx
    cA
    cB
    iblrelem.1
    itgposval.3
    iblpos
    mpbid
    simprd
    recnd
    subid1d
    3eqtrd
end
