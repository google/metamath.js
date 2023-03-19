include "cr.mm"
include "wcel.mm"
include "cxne.mm"
include "cneg.mm"
include "wceq.mm"
include "rexneg.mm"
include "syl.mm"

theorem rexnegd
  let wph: wff ph
  let cA: class A
  assume rexnegd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> -e A = -u A )

  proof
    wph
    cA
    cr
    wcel
    cA
    cxne
    cA
    cneg
    wceq
    rexnegd.1
    cA
    rexneg
    syl
end
