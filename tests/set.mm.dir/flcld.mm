include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "flcl.mm"
include "syl.mm"

theorem flcld
  let wph: wff ph
  let cA: class A
  assume flcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( |_ ` A ) e. ZZ )

  proof
    wph
    cA
    cr
    wcel
    cA
    cfl
    cfv
    cz
    wcel
    flcld.1
    cA
    flcl
    syl
end
