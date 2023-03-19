include "cr.mm"
include "wcel.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "lttri2.mm"
include "syl2anc.mm"

theorem lttri2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A =/= B <-> ( A < B \/ B < A ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    wne
    cA
    cB
    clt
    wbr
    cB
    cA
    clt
    wbr
    wo
    wb
    ltd.1
    ltd.2
    cA
    cB
    lttri2
    syl2anc
end
