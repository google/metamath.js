include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cr.mm"
include "imcl.mm"
include "syl.mm"

theorem imcld
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Im ` A ) e. RR )

  proof
    wph
    cA
    cc
    wcel
    cA
    cim
    cfv
    cr
    wcel
    recld.1
    cA
    imcl
    syl
end
