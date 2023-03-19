include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "halfcl.mm"
include "syl.mm"

theorem halfcld
  let wph: wff ph
  let cA: class A
  assume 2timesd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A / 2 ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    c2
    cdiv
    co
    cc
    wcel
    2timesd.1
    cA
    halfcl
    syl
end
