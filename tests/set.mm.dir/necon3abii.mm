include "wne.mm"
include "wceq.mm"
include "df-ne.mm"
include "xchbinx.mm"

theorem necon3abii
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon3abii.1: |- ( A = B <-> ph )


  assert |- ( A =/= B <-> -. ph )

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
    df-ne
    necon3abii.1
    xchbinx
end
