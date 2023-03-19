include "nsyl3.mm"
include "con2i.mm"

theorem nsyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
