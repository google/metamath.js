include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "times2.mm"
include "syl.mm"

theorem times2d
  let wph: wff ph
  let cA: class A
  assume 2timesd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A x. 2 ) = ( A + A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    c2
    cmul
    co
    cA
    cA
    caddc
    co
    wceq
    2timesd.1
    cA
    times2
    syl
end
