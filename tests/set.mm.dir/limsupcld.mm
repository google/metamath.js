include "wcel.mm"
include "clsp.mm"
include "cfv.mm"
include "cxr.mm"
include "limsupcl.mm"
include "syl.mm"

theorem limsupcld
  let wph: wff ph
  let cF: class F
  let cV: class V
  assume limsupcld.1: |- ( ph -> F e. V )


  assert |- ( ph -> ( limsup ` F ) e. RR* )

  proof
    wph
    cF
    cV
    wcel
    cF
    clsp
    cfv
    cxr
    wcel
    limsupcld.1
    cF
    cV
    limsupcl
    syl
end
