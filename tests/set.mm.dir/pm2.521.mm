include "wi.mm"
include "wn.mm"
include "simplim.mm"
include "a1d.mm"

theorem pm2.521
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) -> ( ps -> ph ) )

  proof
    wph
    wps
    wi
    wn
    wph
    wps
    wph
    wps
    simplim
    a1d
end
