include "crp.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "rpsqrtcl.mm"
include "syl.mm"

theorem rpsqrtcld
  let wph: wff ph
  let cA: class A
  assume sqrgt0d.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( sqrt ` A ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    cA
    csqrt
    cfv
    crp
    wcel
    sqrgt0d.1
    cA
    rpsqrtcl
    syl
end
