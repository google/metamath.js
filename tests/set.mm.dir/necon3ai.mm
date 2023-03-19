include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "nne.mm"
include "sylibr.mm"
include "con2i.mm"

theorem necon3ai
  param wph: wff ph
  param cA: class A
  param cB: class B
  assume necon3ai.1: |- ( ph -> A = B )


  assert |- ( A =/= B -> -. ph )

  proof
    wph
    cA
    cB
    wne
    #
    wph
    cA
    cB
    wceq
    @0
    wn
    necon3ai.1
    cA
    cB
    nne
    sylibr
    con2i
end
