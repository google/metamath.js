include "wne.mm"
include "wceq.mm"
include "nne.mm"
include "xchnxbi.mm"

theorem necon1bbii
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon1bbii.1: |- ( A =/= B <-> ph )


  assert |- ( -. ph <-> A = B )

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    wph
    cA
    cB
    nne
    necon1bbii.1
    xchnxbi
end
