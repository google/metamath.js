include "wi.mm"
include "wn.mm"
include "id.mm"
include "pm2.01.mm"
include "mt2.mm"

theorem bijust
  let wph: wff ph
  let wps: wff ps


  assert |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) )

  proof
    wph
    wps
    wi
    wps
    wph
    wi
    wn
    wi
    wn
    #
    @0
    wi
    #
    @1
    wn
    wi
    @1
    @0
    id
    @1
    pm2.01
    mt2
end
