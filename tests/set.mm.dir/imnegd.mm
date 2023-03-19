include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "imneg.mm"
include "syl.mm"

theorem imnegd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Im ` -u A ) = -u ( Im ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cneg
    cim
    cfv
    cA
    cim
    cfv
    cneg
    wceq
    recld.1
    cA
    imneg
    syl
end
