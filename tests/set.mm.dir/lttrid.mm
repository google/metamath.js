include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "axlttri.mm"
include "syl2anc.mm"

theorem lttrid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A < B <-> -. ( A = B \/ B < A ) ) )

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
    clt
    wbr
    cA
    cB
    wceq
    cB
    cA
    clt
    wbr
    wo
    wn
    wb
    ltd.1
    ltd.2
    cA
    cB
    axlttri
    syl2anc
end
