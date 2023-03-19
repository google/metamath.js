include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "letri3.mm"
include "syl2anc.mm"

theorem letri3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A = B <-> ( A <_ B /\ B <_ A ) ) )

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
    cB
    cA
    cle
    wbr
    wa
    wb
    ltd.1
    ltd.2
    cA
    cB
    letri3
    syl2anc
end
