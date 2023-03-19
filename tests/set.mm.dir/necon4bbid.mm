include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "bicomd.mm"
include "necon4abid.mm"

theorem necon4bbid
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon4bbid.1: |- ( ph -> ( -. ps <-> A =/= B ) )


  assert |- ( ph -> ( ps <-> A = B ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    wph
    wps
    cA
    cB
    wph
    wps
    wn
    cA
    cB
    wne
    necon4bbid.1
    bicomd
    necon4abid
    bicomd
end
