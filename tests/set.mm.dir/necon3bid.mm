include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "necon3bbid.mm"
include "syl5bb.mm"

theorem necon3bid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
