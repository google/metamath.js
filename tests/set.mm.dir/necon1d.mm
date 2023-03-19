include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "nne.mm"
include "syl6ibr.mm"
include "necon4ad.mm"

theorem necon1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon1d.1: |- ( ph -> ( A =/= B -> C = D ) )


  assert |- ( ph -> ( C =/= D -> A = B ) )

  proof
    wph
    cC
    cD
    wne
    #
    cA
    cB
    wph
    cA
    cB
    wne
    cC
    cD
    wceq
    @0
    wn
    necon1d.1
    cC
    cD
    nne
    syl6ibr
    necon4ad
end
