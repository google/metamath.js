include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "syl.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "rnmptss.mm"

theorem rnmptssrn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  assume rnmptssrn.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume rnmptssrn.y: |- ( ( ph /\ x e. A ) -> E. y e. C B = D )

  disjoint A x
  disjoint B y
  disjoint C x
  disjoint D x
  disjoint ph x
  disjoint x y
  assert |- ( ph -> ran ( x e. A |-> B ) C_ ran ( y e. C |-> D ) )

  proof
    wph
    cB
    vy
    cC
    cD
    cmpt
    #
    crn
    #
    wcel
    #
    vx
    cA
    wral
    vx
    cA
    cB
    cmpt
    #
    crn
    @1
    wss
    wph
    @2
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @2
    cB
    cD
    wceq
    vy
    cC
    wrex
    #
    rnmptssrn.y
    @4
    cB
    cV
    wcel
    @2
    @5
    wb
    rnmptssrn.b
    vy
    cC
    cD
    cB
    @0
    cV
    @0
    eqid
    elrnmpt
    syl
    mpbird
    ralrimiva
    vx
    cA
    cB
    @1
    @3
    @3
    eqid
    rnmptss
    syl
end
