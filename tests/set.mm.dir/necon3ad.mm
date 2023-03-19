include "wceq.mm"
include "wne.mm"
include "neneq.mm"
include "nsyli.mm"

theorem necon3ad
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
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
