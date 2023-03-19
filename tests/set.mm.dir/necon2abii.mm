include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "bicomi.mm"
include "necon1abii.mm"

theorem necon2abii
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon2abii.1: |- ( A = B <-> -. ph )


  assert |- ( ph <-> A =/= B )

  proof
    cA
    cB
    wne
    wph
    wph
    cA
    cB
    cA
    cB
    wceq
    wph
    wn
    necon2abii.1
    bicomi
    necon1abii
    bicomi
end
