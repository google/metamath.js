include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "bicomi.mm"
include "necon3abii.mm"

theorem necon3bbii
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon3bbii.1: |- ( ph <-> A = B )


  assert |- ( -. ph <-> A =/= B )

  proof
    cA
    cB
    wne
    wph
    wn
    wph
    cA
    cB
    wph
    cA
    cB
    wceq
    necon3bbii.1
    bicomi
    necon3abii
    bicomi
end
