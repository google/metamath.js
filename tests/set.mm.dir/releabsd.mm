include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "releabs.mm"
include "syl.mm"

theorem releabsd
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Re ` A ) <_ ( abs ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cre
    cfv
    cA
    cabs
    cfv
    cle
    wbr
    abscld.1
    cA
    releabs
    syl
end
