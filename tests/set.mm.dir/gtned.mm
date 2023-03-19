include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "ltne.mm"
include "syl2anc.mm"

theorem gtned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltned.2: |- ( ph -> A < B )


  assert |- ( ph -> B =/= A )

  proof
    wph
    cA
    cr
    wcel
    cA
    cB
    clt
    wbr
    cB
    cA
    wne
    ltd.1
    ltned.2
    cA
    cB
    ltne
    syl2anc
end
