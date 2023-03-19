include "wi.mm"
include "wn.mm"
include "wa.mm"
include "pm2.65.mm"
include "imp.mm"
include "pm2.21.mm"
include "jca.mm"
include "impbii.mm"

theorem pm4.82
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wn
    #
    wi
    #
    wa
    wph
    wn
    #
    @0
    @2
    @3
    wph
    wps
    pm2.65
    imp
    @3
    @0
    @2
    wph
    wps
    pm2.21
    wph
    @1
    pm2.21
    jca
    impbii
end
