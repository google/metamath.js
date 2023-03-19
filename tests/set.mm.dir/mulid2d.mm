include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulid2.mm"
include "syl.mm"

theorem mulid2d
  let wph: wff ph
  let cA: class A
  assume addcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( 1 x. A ) = A )

  proof
    wph
    cA
    cc
    wcel
    c1
    cA
    cmul
    co
    cA
    wceq
    addcld.1
    cA
    mulid2
    syl
end
