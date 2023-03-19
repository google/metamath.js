include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "letric.mm"
include "syl2anc.mm"

theorem letrid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A <_ B \/ B <_ A ) )

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
    cB
    cA
    cle
    wbr
    wo
    ltd.1
    ltd.2
    cA
    cB
    letric
    syl2anc
end
