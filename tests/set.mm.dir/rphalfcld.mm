include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "rphalfcl.mm"
include "syl.mm"

theorem rphalfcld
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A / 2 ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    cA
    c2
    cdiv
    co
    crp
    wcel
    rpred.1
    cA
    rphalfcl
    syl
end
