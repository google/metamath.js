include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "2times.mm"
include "syl.mm"

theorem 2timesd
  let wph: wff ph
  let cA: class A
  assume 2timesd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( 2 x. A ) = ( A + A ) )

  proof
    wph
    cA
    cc
    wcel
    c2
    cA
    cmul
    co
    cA
    cA
    caddc
    co
    wceq
    2timesd.1
    cA
    2times
    syl
end
