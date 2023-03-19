include "wn.mm"
include "wi.mm"
include "con3rr3.mm"
include "con1i.mm"

theorem impi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume impi.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( -. ( ph -> -. ps ) -> ch )

  proof
    wch
    wph
    wps
    wn
    wi
    wph
    wps
    wch
    impi.1
    con3rr3
    con1i
end
