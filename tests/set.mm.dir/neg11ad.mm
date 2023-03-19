include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "neg11.mm"
include "syl2anc.mm"

theorem neg11ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume neg11ad.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( -u A = -u B <-> A = B ) )

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
    wceq
    cA
    cB
    wceq
    wb
    negidd.1
    neg11ad.2
    cA
    cB
    neg11
    syl2anc
end
