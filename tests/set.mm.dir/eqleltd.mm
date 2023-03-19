include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wa.mm"
include "wb.mm"
include "eqlelt.mm"
include "syl2anc.mm"

theorem eqleltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A = B <-> ( A <_ B /\ -. A < B ) ) )

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
    wceq
    cA
    cB
    cle
    wbr
    cA
    cB
    clt
    wbr
    wn
    wa
    wb
    ltd.1
    ltd.2
    cA
    cB
    eqlelt
    syl2anc
end
