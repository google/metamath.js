include "wn.mm"
include "wi.mm"
include "con3rr3.mm"
include "con1i.mm"

theorem impi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
