include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "necon3bbid.mm"
include "syl5bb.mm"

theorem necon3bid
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D
  assume necon3bid.1: |- ( ph -> ( A = B <-> C = D ) )


  assert |- ( ph -> ( A =/= B <-> C =/= D ) )

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    #
    wn
    wph
    cC
    cD
    wne
    cA
    cB
    df-ne
    wph
    @0
    cC
    cD
    necon3bid.1
    necon3bbid
    syl5bb
end
