include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "resqcl.mm"
include "syl.mm"

theorem resqcld
  let wph: wff ph
  let cA: class A
  assume resqcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( A ^ 2 ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    c2
    cexp
    co
    cr
    wcel
    resqcld.1
    cA
    resqcl
    syl
end
