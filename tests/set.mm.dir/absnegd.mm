include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absneg.mm"
include "syl.mm"

theorem absnegd
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( abs ` -u A ) = ( abs ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cneg
    cabs
    cfv
    cA
    cabs
    cfv
    wceq
    abscld.1
    cA
    absneg
    syl
end
