include "wn.mm"
include "wi.mm"
include "pm3.2im.mm"
include "imim1d.mm"
include "com12.mm"

theorem expt
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wph
    wps
    wn
    wi
    wn
    #
    wch
    wi
    wps
    wch
    wi
    wph
    wps
    @0
    wch
    wph
    wps
    pm3.2im
    imim1d
    com12
end
