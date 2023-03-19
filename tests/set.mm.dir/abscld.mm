include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "abscl.mm"
include "syl.mm"

theorem abscld
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( abs ` A ) e. RR )

  proof
    wph
    cA
    cc
    wcel
    cA
    cabs
    cfv
    cr
    wcel
    abscld.1
    cA
    abscl
    syl
end
