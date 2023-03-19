include "wn.mm"
include "wi.mm"
include "pm2.21.mm"
include "imim1i.mm"

theorem jarl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) )

  proof
    wph
    wn
    wph
    wps
    wi
    wch
    wph
    wps
    pm2.21
    imim1i
end
