include "cc.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "cdm.mm"
include "co1.mm"
include "o1f.mm"
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

theorem o1mptrcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let cC: class C
  assume o1add2.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume o1mptrcl.3: |- ( ph -> ( x e. A |-> B ) e. O(1) )

  disjoint A x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint C c
  disjoint C m
  disjoint C n
  disjoint C p
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
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
    co1
    wcel
    @4
    o1mptrcl.3
    @1
    o1f
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
    o1add2.1
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
