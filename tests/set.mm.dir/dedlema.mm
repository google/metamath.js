include "wa.mm"
include "wn.mm"
include "wo.mm"
include "orc.mm"
include "expcom.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "pm2.24.mm"
include "adantld.mm"
include "jaod.mm"
include "impbid.mm"

theorem dedlema
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) )

  proof
    wph
    wps
    wps
    wph
    wa
    #
    wch
    wph
    wn
    #
    wa
    #
    wo
    #
    wps
    wph
    @3
    @0
    @2
    orc
    expcom
    wph
    @0
    wps
    @2
    @0
    wps
    wi
    wph
    wps
    wph
    simpl
    a1i
    wph
    @1
    wps
    wch
    wph
    wps
    pm2.24
    adantld
    jaod
    impbid
end
