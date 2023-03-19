include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "negdi.mm"
include "syl2anc.mm"

theorem negdid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> -u ( A + B ) = ( -u A + -u B ) )

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
    cneg
    caddc
    co
    wceq
    negidd.1
    pncand.2
    cA
    cB
    negdi
    syl2anc
end
