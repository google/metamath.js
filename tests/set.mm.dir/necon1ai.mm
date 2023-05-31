include "wne.mm"
include "wn.mm"
include "necon3ai.mm"
include "notnotrd.mm"

theorem necon1ai
  param wph: wff ph
  param cA: class A
  param cB: class B
  assume necon1ai.1: |- ( -. ph -> A = B )


  assert |- ( A =/= B -> ph )

  proof
    cA
    cB
    wne
    wph
    wph
    wn
    cA
    cB
    necon1ai.1
    necon3ai
    notnotrd
end
