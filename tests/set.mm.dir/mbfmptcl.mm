include "cc.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "cdm.mm"
include "cmbf.mm"
include "mbff.mm"
include "syl.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "feq2d.mm"
include "mpbid.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem mbfmptcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume mbfmptcl.1: |- ( ph -> ( x e. A |-> B ) e. MblFn )
  assume mbfmptcl.2: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A x
  disjoint ph x
  assert |- ( ( ph /\ x e. A ) -> B e. CC )

  proof
    wph
    cB
    cc
    wcel
    #
    vx
    cA
    wph
    cA
    cc
    vx
    cA
    cB
    cmpt
    #
    wf
    #
    @0
    vx
    cA
    wral
    wph
    @1
    cdm
    #
    cc
    @1
    wf
    #
    @2
    wph
    @1
    cmbf
    wcel
    @4
    mbfmptcl.1
    @1
    mbff
    syl
    wph
    @3
    cA
    cc
    @1
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @3
    cA
    wceq
    wph
    @5
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
    feq2d
    mpbid
    vx
    cA
    cc
    cB
    @1
    @1
    eqid
    fmpt
    sylibr
    r19.21bi
end
