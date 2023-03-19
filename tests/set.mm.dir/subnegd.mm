include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subneg.mm"
include "syl2anc.mm"

theorem subnegd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A - -u B ) = ( A + B ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cneg
    cmin
    co
    cA
    cB
    caddc
    co
    wceq
    negidd.1
    pncand.2
    cA
    cB
    subneg
    syl2anc
end
