include "cc0.mm"
include "citg.mm"
include "cle.mm"
include "itgz.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cibl.mm"
include "fconstmpt.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfdm2.mm"
include "ibl0.mm"
include "syl5eqelr.mm"
include "cv.mm"
include "wa.mm"
include "0red.mm"
include "itgle.mm"
include "syl5eqbrr.mm"

theorem itgge0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume itgge0.1: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgge0.2: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgge0.3: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> 0 <_ S. A B _d x )

  proof
    wph
    cc0
    vx
    cA
    cc0
    citg
    vx
    cA
    cB
    citg
    cle
    vx
    cA
    itgz
    wph
    vx
    cA
    cc0
    cB
    wph
    vx
    cA
    cc0
    cmpt
    cA
    cc0
    csn
    cxp
    #
    cibl
    vx
    cA
    cc0
    fconstmpt
    wph
    cA
    cvol
    cdm
    wcel
    @0
    cibl
    wcel
    wph
    vx
    cA
    cB
    cr
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    @1
    cmbf
    wcel
    itgge0.1
    @1
    iblmbf
    syl
    itgge0.2
    mbfdm2
    cA
    ibl0
    syl
    syl5eqelr
    itgge0.1
    wph
    vx
    cv
    cA
    wcel
    wa
    0red
    itgge0.2
    itgge0.3
    itgle
    syl5eqbrr
end
