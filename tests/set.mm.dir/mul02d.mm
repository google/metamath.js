include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul02.mm"
include "syl.mm"

theorem mul02d
  let wph: wff ph
  let cA: class A
  assume muld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( 0 x. A ) = 0 )

  proof
    wph
    cA
    cc
    wcel
    cc0
    cA
    cmul
    co
    cc0
    wceq
    muld.1
    cA
    mul02
    syl
end
