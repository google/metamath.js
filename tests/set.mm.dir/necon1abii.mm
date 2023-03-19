include "wn.mm"
include "wne.mm"
include "notnotb.mm"
include "necon3bbii.mm"
include "bitr2i.mm"

theorem necon1abii
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon1abii.1: |- ( -. ph <-> A = B )


  assert |- ( A =/= B <-> ph )

  proof
    wph
    wph
    wn
    #
    wn
    cA
    cB
    wne
    wph
    notnotb
    @0
    cA
    cB
    necon1abii.1
    necon3bbii
    bitr2i
end
