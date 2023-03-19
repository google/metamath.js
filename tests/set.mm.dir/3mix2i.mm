include "w3o.mm"
include "3mix2.mm"
include "ax-mp.mm"

theorem 3mix2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3mixi.1: |- ph


  assert |- ( ps \/ ph \/ ch )

  proof
    wph
    wps
    wph
    wch
    w3o
    3mixi.1
    wph
    wps
    wch
    3mix2
    ax-mp
end
