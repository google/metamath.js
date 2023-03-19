include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "necon2bbid.mm"
include "nne.mm"
include "syl6rbb.mm"

theorem necon4bid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon4bid.1: |- ( ph -> ( A =/= B <-> C =/= D ) )


  assert |- ( ph -> ( A = B <-> C = D ) )

  proof
    wph
    cC
    cD
    wceq
    cA
    cB
    wne
    #
    wn
    cA
    cB
    wceq
    wph
    @0
    cC
    cD
    necon4bid.1
    necon2bbid
    cA
    cB
    nne
    syl6rbb
end
