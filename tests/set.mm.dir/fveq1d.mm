include "wceq.mm"
include "cfv.mm"
include "fveq1.mm"
include "syl.mm"

theorem fveq1d
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  assume fveq1d.1: |- ( ph -> F = G )


  assert |- ( ph -> ( F ` A ) = ( G ` A ) )

  proof
    wph
    cF
    cG
    wceq
    cA
    cF
    cfv
    cA
    cG
    cfv
    wceq
    fveq1d.1
    cA
    cF
    cG
    fveq1
    syl
end
