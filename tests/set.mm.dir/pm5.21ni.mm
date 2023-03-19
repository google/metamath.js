include "wn.mm"
include "con3i.mm"
include "2falsed.mm"

theorem pm5.21ni
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume pm5.21ni.1: |- ( ph -> ps )
  assume pm5.21ni.2: |- ( ch -> ps )


  assert |- ( -. ps -> ( ph <-> ch ) )

  proof
    wps
    wn
    wph
    wch
    wph
    wps
    pm5.21ni.1
    con3i
    wch
    wps
    pm5.21ni.2
    con3i
    2falsed
end
