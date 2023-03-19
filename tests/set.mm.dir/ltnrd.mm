include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "ltnr.mm"
include "syl.mm"

theorem ltnrd
  let wph: wff ph
  let cA: class A
  assume ltd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> -. A < A )

  proof
    wph
    cA
    cr
    wcel
    cA
    cA
    clt
    wbr
    wn
    ltd.1
    cA
    ltnr
    syl
end
