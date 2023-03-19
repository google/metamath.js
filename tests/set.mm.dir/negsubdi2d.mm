include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "negsubdi2.mm"
include "syl2anc.mm"

theorem negsubdi2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> -u ( A - B ) = ( B - A ) )

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
    cB
    cA
    cmin
    co
    wceq
    negidd.1
    pncand.2
    cA
    cB
    negsubdi2
    syl2anc
end
