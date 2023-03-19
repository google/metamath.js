include "cli.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "climfv.mm"
include "syl.mm"

theorem climfvd
  let wph: wff ph
  let cA: class A
  let cF: class F
  assume climfvd.1: |- ( ph -> F ~~> A )


  assert |- ( ph -> A = ( ~~> ` F ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    cA
    cF
    cli
    cfv
    wceq
    climfvd.1
    cA
    cF
    climfv
    syl
end
