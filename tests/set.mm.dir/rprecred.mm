include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "rpreccld.mm"
include "rpred.mm"

theorem rprecred
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( 1 / A ) e. RR )

  proof
    wph
    c1
    cA
    cdiv
    co
    wph
    cA
    rpred.1
    rpreccld
    rpred
end
