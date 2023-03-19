include "wceq.mm"
include "cqs.mm"
include "qseq2.mm"
include "syl.mm"

theorem qseq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume qseq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C /. A ) = ( C /. B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cqs
    cC
    cB
    cqs
    wceq
    qseq2d.1
    cA
    cB
    cC
    qseq2
    syl
end
