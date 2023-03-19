include "wa.mm"
include "wn.mm"
include "wo.mm"
include "id.mm"
include "orc.mm"
include "adantrr.mm"
include "olc.mm"
include "adantrl.mm"
include "pm2.61ian.mm"
include "jaoi.mm"
include "impbii.mm"

theorem consensus
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) )

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
    wps
    wch
    wa
    #
    wo
    @3
    @3
    @3
    @4
    @3
    id
    wph
    @4
    @3
    wph
    wps
    @3
    wch
    @0
    @2
    orc
    adantrr
    @1
    wch
    @3
    wps
    @2
    @0
    olc
    adantrl
    pm2.61ian
    jaoi
    @3
    @4
    orc
    impbii
end
