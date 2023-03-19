include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "div1.mm"
include "syl.mm"

theorem div1d
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A / 1 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    c1
    cdiv
    co
    cA
    wceq
    div1d.1
    cA
    div1
    syl
end
