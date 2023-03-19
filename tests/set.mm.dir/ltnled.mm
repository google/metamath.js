include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "wb.mm"
include "ltnle.mm"
include "syl2anc.mm"

theorem ltnled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A < B <-> -. B <_ A ) )

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
    cB
    cA
    cle
    wbr
    wn
    wb
    ltd.1
    ltd.2
    cA
    cB
    ltnle
    syl2anc
end
