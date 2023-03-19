include "wn.mm"
include "con3d.mm"
include "syl5.mm"

theorem nsyli
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nsyli.1: |- ( ph -> ( ps -> ch ) )
  assume nsyli.2: |- ( th -> -. ch )


  assert |- ( ph -> ( th -> -. ps ) )

  proof
    wth
    wch
    wn
    wph
    wps
    wn
    nsyli.2
    wph
    wps
    wch
    nsyli.1
    con3d
    syl5
end
