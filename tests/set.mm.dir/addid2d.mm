include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addid2.mm"
include "syl.mm"

theorem addid2d
  let wph: wff ph
  let cA: class A
  assume muld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( 0 + A ) = A )

  proof
    wph
    cA
    cc
    wcel
    cc0
    cA
    caddc
    co
    cA
    wceq
    muld.1
    cA
    addid2
    syl
end
