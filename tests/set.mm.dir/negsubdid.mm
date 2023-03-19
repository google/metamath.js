include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "wceq.mm"
include "negsubdi.mm"
include "syl2anc.mm"

theorem negsubdid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> -u ( A - B ) = ( -u A + B ) )

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
    cmin
    co
    cneg
    cA
    cneg
    cB
    caddc
    co
    wceq
    negidd.1
    pncand.2
    cA
    cB
    negsubdi
    syl2anc
end
