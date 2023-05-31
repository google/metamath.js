include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "necon3ad.mm"
include "df-ne.mm"
include "syl6ibr.mm"

theorem necon3d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D
  assume necon3d.1: |- ( ph -> ( A = B -> C = D ) )


  assert |- ( ph -> ( C =/= D -> A =/= B ) )

  proof
    wph
    cC
    cD
    wne
    cA
    cB
    wceq
    #
    wn
    cA
    cB
    wne
    wph
    @0
    cC
    cD
    necon3d.1
    necon3ad
    cA
    cB
    df-ne
    syl6ibr
end
