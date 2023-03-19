include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "leloe.mm"
include "syl2anc.mm"

theorem leloed
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A <_ B <-> ( A < B \/ A = B ) ) )

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
    cA
    cB
    wceq
    wo
    wb
    ltd.1
    ltd.2
    cA
    cB
    leloe
    syl2anc
end
