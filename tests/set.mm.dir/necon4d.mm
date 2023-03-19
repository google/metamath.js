include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "necon2bd.mm"
include "nne.mm"
include "syl6ib.mm"

theorem necon4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon4d.1: |- ( ph -> ( A =/= B -> C =/= D ) )


  assert |- ( ph -> ( C = D -> A = B ) )

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
    necon4d.1
    necon2bd
    cA
    cB
    nne
    syl6ib
end
