include "cre.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cim.mm"
include "wa.mm"
include "cv.mm"
include "cdif.mm"
include "fveq2d.mm"
include "recld.mm"
include "mbfeqalem.mm"
include "imcld.mm"
include "anbi12d.mm"
include "ismbfcn2.mm"
include "3bitr4d.mm"

theorem mbfeqa
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z
  let vy: setvar y
  assume mbfeqa.1: |- ( ph -> A C_ RR )
  assume mbfeqa.2: |- ( ph -> ( vol* ` A ) = 0 )
  assume mbfeqa.3: |- ( ( ph /\ x e. ( B \ A ) ) -> C = D )
  assume mbfeqa.4: |- ( ( ph /\ x e. B ) -> C e. CC )
  assume mbfeqa.5: |- ( ( ph /\ x e. B ) -> D e. CC )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint x z
  disjoint A z
  disjoint x y
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( ( x e. B |-> C ) e. MblFn <-> ( x e. B |-> D ) e. MblFn ) )

  proof
    wph
    vx
    cB
    cC
    cre
    cfv
    #
    cmpt
    cmbf
    wcel
    #
    vx
    cB
    cC
    cim
    cfv
    #
    cmpt
    cmbf
    wcel
    #
    wa
    vx
    cB
    cD
    cre
    cfv
    #
    cmpt
    cmbf
    wcel
    #
    vx
    cB
    cD
    cim
    cfv
    #
    cmpt
    cmbf
    wcel
    #
    wa
    vx
    cB
    cC
    cmpt
    cmbf
    wcel
    vx
    cB
    cD
    cmpt
    cmbf
    wcel
    wph
    @1
    @5
    @3
    @7
    wph
    vx
    cA
    cB
    @0
    @4
    mbfeqa.1
    mbfeqa.2
    wph
    vx
    cv
    #
    cB
    cA
    cdif
    wcel
    wa
    #
    cC
    cD
    cre
    mbfeqa.3
    fveq2d
    wph
    @8
    cB
    wcel
    wa
    #
    cC
    mbfeqa.4
    recld
    @10
    cD
    mbfeqa.5
    recld
    mbfeqalem
    wph
    vx
    cA
    cB
    @2
    @6
    mbfeqa.1
    mbfeqa.2
    @9
    cC
    cD
    cim
    mbfeqa.3
    fveq2d
    @10
    cC
    mbfeqa.4
    imcld
    @10
    cD
    mbfeqa.5
    imcld
    mbfeqalem
    anbi12d
    wph
    vx
    cB
    cC
    mbfeqa.4
    ismbfcn2
    wph
    vx
    cB
    cD
    mbfeqa.5
    ismbfcn2
    3bitr4d
end
