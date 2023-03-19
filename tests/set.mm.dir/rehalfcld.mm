include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "rehalfcl.mm"
include "syl.mm"

theorem rehalfcld
  let wph: wff ph
  let cA: class A
  assume rehalfcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( A / 2 ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    c2
    cdiv
    co
    cr
    wcel
    rehalfcld.1
    cA
    rehalfcl
    syl
end
