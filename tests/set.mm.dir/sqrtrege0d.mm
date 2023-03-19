include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "csqrt.mm"
include "cfv.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "sqrtrege0.mm"
include "syl.mm"

theorem sqrtrege0d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> 0 <_ ( Re ` ( sqrt ` A ) ) )

  proof
    wph
    cA
    cc
    wcel
    cc0
    cA
    csqrt
    cfv
    cre
    cfv
    cle
    wbr
    abscld.1
    cA
    sqrtrege0
    syl
end
