include "wn.mm"
include "wi.mm"
include "id.mm"
include "idd.mm"
include "jad.mm"

theorem pm2.6
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wn
    wps
    wi
    #
    wph
    wps
    wps
    @0
    id
    @0
    wps
    idd
    jad
end
