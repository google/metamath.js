include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cim.mm"
include "cneg.mm"
include "wceq.mm"
include "imcj.mm"
include "syl.mm"

theorem imcjd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( Im ` ( * ` A ) ) = -u ( Im ` A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccj
    cfv
    cim
    cfv
    cA
    cim
    cfv
    cneg
    wceq
    recld.1
    cA
    imcj
    syl
end
