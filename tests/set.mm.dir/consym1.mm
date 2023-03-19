include "wfal.mm"
include "wa.mm"
include "wi.mm"
include "falim.mm"
include "ad2antll.mm"
include "pm2.43i.mm"

theorem consym1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps /\ ( ps /\ F. ) ) -> ( ps /\ ph ) )

  proof
    wps
    wps
    wfal
    wa
    wa
    #
    wps
    wph
    wa
    #
    wfal
    @0
    @1
    wi
    #
    wps
    wps
    @2
    falim
    ad2antll
    pm2.43i
end
