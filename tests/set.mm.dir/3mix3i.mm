include "w3o.mm"
include "3mix3.mm"
include "ax-mp.mm"

theorem 3mix3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3mixi.1: |- ph


  assert |- ( ps \/ ch \/ ph )

  proof
    wph
    wps
    wch
    wph
    w3o
    3mixi.1
    wph
    wps
    wch
    3mix3
    ax-mp
end
