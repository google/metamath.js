include "wn.mm"
include "wceq.mm"
include "wne.mm"
include "bicomi.mm"
include "necon1bbii.mm"

theorem necon2bbii
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon2bbii.1: |- ( ph <-> A =/= B )


  assert |- ( A = B <-> -. ph )

  proof
    wph
    wn
    cA
    cB
    wceq
    wph
    cA
    cB
    wph
    cA
    cB
    wne
    necon2bbii.1
    bicomi
    necon1bbii
    bicomi
end
