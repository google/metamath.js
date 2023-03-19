include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul01.mm"
include "syl.mm"

theorem mul01d
  let wph: wff ph
  let cA: class A
  assume muld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A x. 0 ) = 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    cmul
    co
    cc0
    wceq
    muld.1
    cA
    mul01
    syl
end
