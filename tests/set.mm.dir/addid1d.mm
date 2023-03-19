include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addid1.mm"
include "syl.mm"

theorem addid1d
  let wph: wff ph
  let cA: class A
  assume muld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A + 0 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    caddc
    co
    cA
    wceq
    muld.1
    cA
    addid1
    syl
end
