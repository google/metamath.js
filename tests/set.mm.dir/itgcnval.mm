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
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "recld.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "itgrevallem1.mm"
include "imcld.mm"
include "simprd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"

theorem itgcnval
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
  assert |- ( ph -> S. A B _d x = ( S. A ( Re ` B ) _d x + ( _i x. S. A ( Im ` B ) _d x ) ) )

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
    cmpt
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
    @3
    cc0
    cif
    cmpt
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
    @6
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
    @6
    cneg
    #
    cle
    wbr
    wa
    @8
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
    cA
    @1
    citg
    #
    ci
    vx
    cA
    @6
    citg
    #
    cmul
    co
    #
    caddc
    co
    wph
    vx
    cA
    cB
    @2
    @4
    @7
    @9
    cV
    @2
    eqid
    @4
    eqid
    @7
    eqid
    @9
    eqid
    itgcnval.1
    itgcnval.2
    itgcnlem
    wph
    @12
    @5
    @14
    @11
    caddc
    wph
    vx
    cA
    @1
    wph
    @0
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
    @16
    cmbf
    wcel
    itgcnval.2
    @16
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
    @6
    cmpt
    cibl
    wcel
    #
    wph
    @17
    @19
    @20
    wa
    itgcnval.2
    wph
    vx
    cA
    cB
    @18
    iblcn
    mpbid
    #
    simpld
    itgrevallem1
    wph
    @13
    @10
    ci
    cmul
    wph
    vx
    cA
    @6
    @15
    cB
    @18
    imcld
    wph
    @19
    @20
    @21
    simprd
    itgrevallem1
    oveq2d
    oveq12d
    eqtr4d
end
