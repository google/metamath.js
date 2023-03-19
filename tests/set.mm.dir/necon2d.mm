include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "df-ne.mm"
include "syl6ib.mm"
include "necon2ad.mm"

theorem necon2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon2d.1: |- ( ph -> ( A = B -> C =/= D ) )


  assert |- ( ph -> ( C = D -> A =/= B ) )

  proof
    wph
    cC
    cD
    wceq
    #
    cA
    cB
    wph
    cA
    cB
    wceq
    cC
    cD
    wne
    @0
    wn
    necon2d.1
    cC
    cD
    df-ne
    syl6ib
    necon2ad
end
