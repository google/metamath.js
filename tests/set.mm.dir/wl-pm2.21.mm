include "wn.mm"
include "ax-luk3.mm"
include "wl-com12.mm"

theorem wl-pm2.21
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ph -> ps ) )

  proof
    wph
    wph
    wn
    wps
    wph
    wps
    ax-luk3
    wl-com12
end
