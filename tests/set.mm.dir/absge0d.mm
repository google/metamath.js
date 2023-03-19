include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "absge0.mm"
include "syl.mm"

theorem absge0d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> 0 <_ ( abs ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cc0
    cA
    cabs
    cfv
    cle
    wbr
    abscld.1
    cA
    absge0
    syl
end
