include "wceq.mm"
include "wne.mm"
include "neneq.mm"
include "nsyli.mm"

theorem necon3ad
  param wph: wff ph
  param wps: wff ps
  param cA: class A
  param cB: class B
  assume necon3ad.1: |- ( ph -> ( ps -> A = B ) )


  assert |- ( ph -> ( A =/= B -> -. ps ) )

  proof
    wph
    wps
    cA
    cB
    wceq
    cA
    cB
    wne
    necon3ad.1
    cA
    cB
    neneq
    nsyli
end
