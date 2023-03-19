include "wvhc2.mm"
include "wvd1.mm"
include "wa.mm"
include "wi.mm"
include "simpr.mm"
include "dfvd2an.mm"
include "mpbir.mm"

theorem iden2
  let wph: wff ph
  let wps: wff ps


  assert |- (. (. ph ,. ps ). ->. ps ).

  proof
    wph
    wps
    wvhc2
    wps
    wvd1
    wph
    wps
    wa
    wps
    wi
    wph
    wps
    simpr
    wph
    wps
    wps
    dfvd2an
    mpbir
end
