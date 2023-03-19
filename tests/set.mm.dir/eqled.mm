include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "eqle.mm"
include "syl2anc.mm"

theorem eqled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume eqled.1: |- ( ph -> A e. RR )
  assume eqled.2: |- ( ph -> A = B )


  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cr
    wcel
    cA
    cB
    wceq
    cA
    cB
    cle
    wbr
    eqled.1
    eqled.2
    cA
    cB
    eqle
    syl2anc
end
