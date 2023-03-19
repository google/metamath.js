include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "subid.mm"
include "syl.mm"

theorem subidd
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A - A ) = 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cA
    cmin
    co
    cc0
    wceq
    negidd.1
    cA
    subid
    syl
end
