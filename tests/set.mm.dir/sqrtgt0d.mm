include "csqrt.mm"
include "cfv.mm"
include "rpsqrtcld.mm"
include "rpgt0d.mm"

theorem sqrtgt0d
  let wph: wff ph
  let cA: class A
  assume sqrgt0d.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> 0 < ( sqrt ` A ) )

  proof
    wph
    cA
    csqrt
    cfv
    wph
    cA
    sqrgt0d.1
    rpsqrtcld
    rpgt0d
end
