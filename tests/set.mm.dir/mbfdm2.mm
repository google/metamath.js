include "cmpt.mm"
include "cdm.mm"
include "cvol.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "cmbf.mm"
include "mbfdm.mm"
include "eqeltrrd.mm"

theorem mbfdm2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume mbfmptcl.1: |- ( ph -> ( x e. A |-> B ) e. MblFn )
  assume mbfmptcl.2: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> A e. dom vol )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    cA
    cvol
    cdm
    #
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @1
    cA
    wceq
    wph
    @3
    vx
    cA
    mbfmptcl.2
    ralrimiva
    vx
    cA
    cB
    cV
    dmmptg
    syl
    wph
    @0
    cmbf
    wcel
    @1
    @2
    wcel
    mbfmptcl.1
    @0
    mbfdm
    syl
    eqeltrrd
end
