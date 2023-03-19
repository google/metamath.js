include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "bicomd.mm"
include "necon3abid.mm"

theorem necon3bbid
  param wph: wff ph
  param wps: wff ps
  param cA: class A
  param cB: class B
  assume necon3bbid.1: |- ( ph -> ( ps <-> A = B ) )


  assert |- ( ph -> ( -. ps <-> A =/= B ) )

  proof
    wph
    cA
    cB
    wne
    wps
    wn
    wph
    wps
    cA
    cB
    wph
    wps
    cA
    cB
    wceq
    necon3bbid.1
    bicomd
    necon3abid
    bicomd
end
