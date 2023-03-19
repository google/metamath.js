include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "subeq0.mm"
include "syl2anc.mm"

theorem subeq0ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A - B ) = 0 <-> A = B ) )

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
    cc0
    wceq
    cA
    cB
    wceq
    wb
    negidd.1
    pncand.2
    cA
    cB
    subeq0
    syl2anc
end
