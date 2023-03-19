include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "neg2sub.mm"
include "syl2anc.mm"

theorem neg2subd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( -u A - -u B ) = ( B - A ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cneg
    cB
    cneg
    cmin
    co
    cB
    cA
    cmin
    co
    wceq
    negidd.1
    pncand.2
    cA
    cB
    neg2sub
    syl2anc
end
