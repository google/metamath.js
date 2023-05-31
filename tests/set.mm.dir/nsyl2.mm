include "wn.mm"
include "wi.mm"
include "a1i.mm"
include "mt3d.mm"

theorem nsyl2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume nsyl2.1: |- ( ph -> -. ps )
  assume nsyl2.2: |- ( -. ch -> ps )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wps
    nsyl2.1
    wch
    wn
    wps
    wi
    wph
    nsyl2.2
    a1i
    mt3d
end
