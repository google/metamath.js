include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulm1.mm"
include "syl.mm"

theorem mulm1d
  let wph: wff ph
  let cA: class A
  assume mulm1d.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( -u 1 x. A ) = -u A )

  proof
    wph
    cA
    cc
    wcel
    c1
    cneg
    cA
    cmul
    co
    cA
    cneg
    wceq
    mulm1d.1
    cA
    mulm1
    syl
end
