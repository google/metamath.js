include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wne.mm"
include "wb.mm"
include "leltne.mm"
include "syl3anc.mm"

theorem leltned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume leltned.3: |- ( ph -> A <_ B )


  assert |- ( ph -> ( A < B <-> B =/= A ) )

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
    cle
    wbr
    cA
    cB
    clt
    wbr
    cB
    cA
    wne
    wb
    ltd.1
    ltd.2
    leltned.3
    cA
    cB
    leltne
    syl3anc
end
