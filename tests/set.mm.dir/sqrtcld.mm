include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "sqrtcl.mm"
include "syl.mm"

theorem sqrtcld
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( sqrt ` A ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    csqrt
    cfv
    cc
    wcel
    abscld.1
    cA
    sqrtcl
    syl
end
