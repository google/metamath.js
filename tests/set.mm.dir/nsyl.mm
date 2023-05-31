include "nsyl3.mm"
include "con2i.mm"

theorem nsyl
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume nsyl.1: |- ( ph -> -. ps )
  assume nsyl.2: |- ( ch -> ps )


  assert |- ( ph -> -. ch )

  proof
    wch
    wph
    wph
    wps
    wch
    nsyl.1
    nsyl.2
    nsyl3
    con2i
end
