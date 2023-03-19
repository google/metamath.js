include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cneg.mm"
include "cmin.mm"
include "wceq.mm"
include "negdi2.mm"
include "syl2anc.mm"

theorem negdi2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> -u ( A + B ) = ( -u A - B ) )

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
    caddc
    co
    cneg
    cA
    cneg
    cB
    cmin
    co
    wceq
    negidd.1
    pncand.2
    cA
    cB
    negdi2
    syl2anc
end
