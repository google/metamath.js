include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "lttri4.mm"
include "syl2anc.mm"

theorem lttri4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A < B \/ A = B \/ B < A ) )

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
    w3o
    ltd.1
    ltd.2
    cA
    cB
    lttri4
    syl2anc
end
