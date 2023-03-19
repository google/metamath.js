include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "elrnmpt.mm"
include "syl.mm"
include "mpbird.mm"

theorem elrnmptd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  assume elrnmptd.f: |- F = ( x e. A |-> B )
  assume elrnmptd.x: |- ( ph -> E. x e. A C = B )
  assume elrnmptd.c: |- ( ph -> C e. V )

  disjoint C x
  assert |- ( ph -> C e. ran F )

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
    vx
    cA
    wrex
    #
    elrnmptd.x
    wph
    cC
    cV
    wcel
    @0
    @1
    wb
    elrnmptd.c
    vx
    cA
    cB
    cC
    cF
    cV
    elrnmptd.f
    elrnmpt
    syl
    mpbird
end
