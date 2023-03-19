include "citg.mm"
include "cim.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "itgcnval.mm"
include "fveq2d.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "recld.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "itgrecl.mm"
include "imcld.mm"
include "simprd.mm"
include "crimd.mm"
include "eqtrd.mm"

theorem itgim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume itgcnval.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgcnval.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint V x
  assert |- ( ph -> ( Im ` S. A B _d x ) = S. A ( Im ` B ) _d x )

  proof
    wph
    vx
    cA
    cB
    citg
    #
    cim
    cfv
    vx
    cA
    cB
    cre
    cfv
    #
    citg
    #
    ci
    vx
    cA
    cB
    cim
    cfv
    #
    citg
    #
    cmul
    co
    caddc
    co
    #
    cim
    cfv
    @4
    wph
    @0
    @5
    cim
    wph
    vx
    cA
    cB
    cV
    itgcnval.1
    itgcnval.2
    itgcnval
    fveq2d
    wph
    @2
    @4
    wph
    vx
    cA
    @1
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    #
    @7
    cmbf
    wcel
    itgcnval.2
    @7
    iblmbf
    syl
    itgcnval.1
    mbfmptcl
    #
    recld
    wph
    vx
    cA
    @1
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @3
    cmpt
    cibl
    wcel
    #
    wph
    @8
    @10
    @11
    wa
    itgcnval.2
    wph
    vx
    cA
    cB
    @9
    iblcn
    mpbid
    #
    simpld
    itgrecl
    wph
    vx
    cA
    @3
    @6
    cB
    @9
    imcld
    wph
    @10
    @11
    @12
    simprd
    itgrecl
    crimd
    eqtrd
end
