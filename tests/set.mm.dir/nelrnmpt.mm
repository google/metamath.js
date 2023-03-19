include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "wn.mm"
include "wral.mm"
include "cv.mm"
include "wa.mm"
include "neneqd.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralnex.mm"
include "sylib.mm"
include "wb.mm"
include "elrnmpt.mm"
include "syl.mm"
include "mtbird.mm"

theorem nelrnmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  assume nelrnmpt.x: |- F/ x ph
  assume nelrnmpt.f: |- F = ( x e. A |-> B )
  assume nelrnmpt.c: |- ( ph -> C e. V )
  assume nelrnmpt.n: |- ( ( ph /\ x e. A ) -> C =/= B )

  disjoint C x
  assert |- ( ph -> -. C e. ran F )

  proof
    wph
    cC
    cF
    crn
    wcel
    #
    cC
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    wph
    @1
    wn
    #
    vx
    cA
    wral
    @2
    wn
    wph
    @3
    vx
    cA
    nelrnmpt.x
    wph
    vx
    cv
    cA
    wcel
    #
    @3
    wph
    @4
    wa
    cC
    cB
    nelrnmpt.n
    neneqd
    ex
    ralrimi
    @1
    vx
    cA
    ralnex
    sylib
    wph
    cC
    cV
    wcel
    @0
    @2
    wb
    nelrnmpt.c
    vx
    cA
    cB
    cC
    cF
    cV
    nelrnmpt.f
    elrnmpt
    syl
    mtbird
end
