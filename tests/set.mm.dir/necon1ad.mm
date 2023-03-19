include "wne.mm"
include "wn.mm"
include "necon3ad.mm"
include "notnotr.mm"
include "syl6.mm"

theorem necon1ad
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon1ad.1: |- ( ph -> ( -. ps -> A = B ) )


  assert |- ( ph -> ( A =/= B -> ps ) )

  proof
    wph
    cA
    cB
    wne
    wps
    wn
    #
    wn
    wps
    wph
    @0
    cA
    cB
    necon1ad.1
    necon3ad
    wps
    notnotr
    syl6
end
