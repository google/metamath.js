include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulid1.mm"
include "syl.mm"

theorem mulid1d
  let wph: wff ph
  let cA: class A
  assume addcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A x. 1 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    c1
    cmul
    co
    cA
    wceq
    addcld.1
    cA
    mulid1
    syl
end
