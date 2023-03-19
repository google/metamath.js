include "wceq.mm"
include "cqs.mm"
include "qseq1.mm"
include "syl.mm"

theorem qseq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume qseq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A /. C ) = ( B /. C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cqs
    cB
    cC
    cqs
    wceq
    qseq1d.1
    cA
    cB
    cC
    qseq1
    syl
end
