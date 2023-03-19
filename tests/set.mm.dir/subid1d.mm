include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "subid1.mm"
include "syl.mm"

theorem subid1d
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A - 0 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    cmin
    co
    cA
    wceq
    negidd.1
    cA
    subid1
    syl
end
