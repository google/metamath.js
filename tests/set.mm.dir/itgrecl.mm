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
include "cmbf.mm"
include "w3a.mm"
include "cibl.mm"
include "iblrelem.mm"
include "mpbid.mm"
include "resubcl.mm"
include "3adant1.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem itgrecl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume itgrecl.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgrecl.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> S. A B _d x e. RR )

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
    wa
    cB
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
    cB
    cneg
    #
    cle
    wbr
    wa
    @2
    cc0
    cif
    cmpt
    citg2
    cfv
    #
    cmin
    co
    #
    cr
    wph
    vx
    cA
    cB
    itgrecl.1
    itgrecl.2
    itgrevallem1
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @1
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    w3a
    #
    @4
    cr
    wcel
    #
    wph
    @5
    cibl
    wcel
    @9
    itgrecl.2
    wph
    vx
    cA
    cB
    itgrecl.1
    iblrelem
    mpbid
    @7
    @8
    @10
    @6
    @1
    @3
    resubcl
    3adant1
    syl
    eqeltrd
end
