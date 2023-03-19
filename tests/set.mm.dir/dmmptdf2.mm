include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "cdm.mm"
include "wral.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "elex.mm"
include "syl.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabid2f.mm"
include "sylibr.mm"
include "dmmpt.mm"
include "syl6reqr.mm"

theorem dmmptdf2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume dmmptdf2.x: |- F/ x ph
  assume dmmptdf2.b: |- F/_ x B
  assume dmmptdf2.a: |- A = ( x e. B |-> C )
  assume dmmptdf2.c: |- ( ( ph /\ x e. B ) -> C e. V )


  assert |- ( ph -> dom A = B )

  proof
    wph
    cB
    cC
    cvv
    wcel
    #
    vx
    cB
    crab
    #
    cA
    cdm
    wph
    @0
    vx
    cB
    wral
    cB
    @1
    wceq
    wph
    @0
    vx
    cB
    dmmptdf2.x
    wph
    vx
    cv
    cB
    wcel
    #
    @0
    wph
    @2
    wa
    cC
    cV
    wcel
    @0
    dmmptdf2.c
    cC
    cV
    elex
    syl
    ex
    ralrimi
    @0
    vx
    cB
    dmmptdf2.b
    rabid2f
    sylibr
    vx
    cB
    cC
    cA
    dmmptdf2.a
    dmmpt
    syl6reqr
end
