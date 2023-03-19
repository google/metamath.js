include "cc.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "cdm.mm"
include "crli.mm"
include "wbr.mm"
include "rlimf.mm"
include "syl.mm"
include "eqid.mm"
include "dmmptd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem rlimmptrcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rlimabs.1: |- ( ( ph /\ k e. A ) -> B e. V )
  assume rlimabs.2: |- ( ph -> ( k e. A |-> B ) ~~>r C )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  assert |- ( ( ph /\ k e. A ) -> B e. CC )

  proof
    wph
    cB
    cc
    wcel
    #
    vk
    cA
    wph
    cA
    cc
    vk
    cA
    cB
    cmpt
    #
    wf
    #
    @0
    vk
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
    cC
    crli
    wbr
    @4
    rlimabs.2
    cC
    @1
    rlimf
    syl
    wph
    @3
    cA
    cc
    @1
    wph
    vk
    @1
    cA
    cB
    cV
    @1
    eqid
    #
    rlimabs.1
    dmmptd
    feq2d
    mpbid
    vk
    cA
    cc
    cB
    @1
    @5
    fmpt
    sylibr
    r19.21bi
end
