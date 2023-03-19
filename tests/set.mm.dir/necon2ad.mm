include "wn.mm"
include "wne.mm"
include "notnot.mm"
include "necon3bd.mm"
include "syl5.mm"

theorem necon2ad
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon2ad.1: |- ( ph -> ( A = B -> -. ps ) )


  assert |- ( ph -> ( ps -> A =/= B ) )

  proof
    wps
    wps
    wn
    #
    wn
    wph
    cA
    cB
    wne
    wps
    notnot
    wph
    @0
    cA
    cB
    necon2ad.1
    necon3bd
    syl5
end
