include "wcel.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "fvres.mm"
include "syl.mm"

theorem fvresd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume fvresd.1: |- ( ph -> A e. B )


  assert |- ( ph -> ( ( F |` B ) ` A ) = ( F ` A ) )

  proof
    wph
    cA
    cB
    wcel
    cA
    cF
    cB
    cres
    cfv
    cA
    cF
    cfv
    wceq
    fvresd.1
    cA
    cB
    cF
    fvres
    syl
end
