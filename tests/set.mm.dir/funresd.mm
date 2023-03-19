include "wfun.mm"
include "cres.mm"
include "funres.mm"
include "syl.mm"

theorem funresd
  let wph: wff ph
  let cA: class A
  let cF: class F
  assume funresd.1: |- ( ph -> Fun F )


  assert |- ( ph -> Fun ( F |` A ) )

  proof
    wph
    cF
    wfun
    cF
    cA
    cres
    wfun
    funresd.1
    cA
    cF
    funres
    syl
end
