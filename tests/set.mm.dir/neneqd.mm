include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "sylib.mm"

theorem neneqd
  param wph: wff ph
  param cA: class A
  param cB: class B
  assume neneqd.1: |- ( ph -> A =/= B )


  assert |- ( ph -> -. A = B )

  proof
    wph
    cA
    cB
    wne
    cA
    cB
    wceq
    wn
    neneqd.1
    cA
    cB
    df-ne
    sylib
end
