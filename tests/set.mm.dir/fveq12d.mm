include "cfv.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem fveq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume fveq12d.1: |- ( ph -> F = G )
  assume fveq12d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( F ` A ) = ( G ` B ) )

  proof
    wph
    cA
    cF
    cfv
    cA
    cG
    cfv
    cB
    cG
    cfv
    wph
    cA
    cF
    cG
    fveq12d.1
    fveq1d
    wph
    cA
    cB
    cG
    fveq12d.2
    fveq2d
    eqtrd
end
