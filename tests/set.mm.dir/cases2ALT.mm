include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "pm3.4.mm"
include "pm2.24.mm"
include "adantr.mm"
include "jca.mm"
include "pm2.21.mm"
include "jaoi.mm"
include "pm2.27.mm"
include "imdistani.mm"
include "orcd.mm"
include "adantrr.mm"
include "olcd.mm"
include "adantrl.mm"
include "pm2.61ian.mm"
include "impbii.mm"

theorem cases2ALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) <-> ( ( ph -> ps ) /\ ( -. ph -> ch ) ) )

  proof
    wph
    wps
    wa
    #
    wph
    wn
    #
    wch
    wa
    #
    wo
    #
    wph
    wps
    wi
    #
    @1
    wch
    wi
    #
    wa
    #
    @0
    @6
    @2
    @0
    @4
    @5
    wph
    wps
    pm3.4
    wph
    @5
    wps
    wph
    wch
    pm2.24
    adantr
    jca
    @2
    @4
    @5
    @1
    @4
    wch
    wph
    wps
    pm2.21
    adantr
    @1
    wch
    pm3.4
    jca
    jaoi
    wph
    @6
    @3
    wph
    @4
    @3
    @5
    wph
    @4
    wa
    @0
    @2
    wph
    @4
    wps
    wph
    wps
    pm2.27
    imdistani
    orcd
    adantrr
    @1
    @5
    @3
    @4
    @1
    @5
    wa
    @2
    @0
    @1
    @5
    wch
    @1
    wch
    pm2.27
    imdistani
    olcd
    adantrl
    pm2.61ian
    impbii
end
