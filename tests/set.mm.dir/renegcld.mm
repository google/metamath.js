include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "renegcl.mm"
include "syl.mm"

theorem renegcld
  let wph: wff ph
  let cA: class A
  assume renegcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> -u A e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    cneg
    cr
    wcel
    renegcld.1
    cA
    renegcl
    syl
end
