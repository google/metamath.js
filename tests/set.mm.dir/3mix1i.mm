include "w3o.mm"
include "3mix1.mm"
include "ax-mp.mm"

theorem 3mix1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3mixi.1: |- ph


  assert |- ( ph \/ ps \/ ch )

  proof
    wph
    wph
    wps
    wch
    w3o
    3mixi.1
    wph
    wps
    wch
    3mix1
    ax-mp
end
