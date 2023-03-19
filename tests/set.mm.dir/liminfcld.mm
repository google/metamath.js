include "wcel.mm"
include "clsi.mm"
include "cfv.mm"
include "cxr.mm"
include "liminfcl.mm"
include "syl.mm"

theorem liminfcld
  let wph: wff ph
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume liminfcld.1: |- ( ph -> F e. V )


  assert |- ( ph -> ( liminf ` F ) e. RR* )

  proof
    wph
    cF
    cV
    wcel
    cF
    clsi
    cfv
    cxr
    wcel
    liminfcld.1
    cF
    cV
    liminfcl
    syl
end
