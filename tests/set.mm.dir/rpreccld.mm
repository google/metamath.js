include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "rpreccl.mm"
include "syl.mm"

theorem rpreccld
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( 1 / A ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    c1
    cA
    cdiv
    co
    crp
    wcel
    rpred.1
    cA
    rpreccl
    syl
end
