include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "negcon1.mm"
include "syl2anc.mm"

theorem negcon1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume negcon1d.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( -u A = B <-> -u B = A ) )

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
    wceq
    cB
    cneg
    cA
    wceq
    wb
    negidd.1
    negcon1d.2
    cA
    cB
    negcon1
    syl2anc
end
