include "wn.mm"
include "wceq.mm"
include "notnot.mm"
include "necon1bd.mm"
include "syl5.mm"

theorem necon4ad
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon4ad.1: |- ( ph -> ( A =/= B -> -. ps ) )


  assert |- ( ph -> ( ps -> A = B ) )

  proof
    wps
    wps
    wn
    #
    wn
    wph
    cA
    cB
    wceq
    wps
    notnot
    wph
    @0
    cA
    cB
    necon4ad.1
    necon1bd
    syl5
end
