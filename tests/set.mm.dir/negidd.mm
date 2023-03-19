include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "negid.mm"
include "syl.mm"

theorem negidd
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A + -u A ) = 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cA
    cneg
    caddc
    co
    cc0
    wceq
    negidd.1
    cA
    negid
    syl
end
