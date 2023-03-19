include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "ltlen.mm"
include "syl2anc.mm"

theorem ltlend
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A < B <-> ( A <_ B /\ B =/= A ) ) )

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
    cle
    wbr
    cB
    cA
    wne
    wa
    wb
    ltd.1
    ltd.2
    cA
    cB
    ltlen
    syl2anc
end
