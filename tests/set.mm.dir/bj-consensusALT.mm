include "wif.mm"
include "wa.mm"
include "wo.mm"
include "orcom.mm"
include "wi.mm"
include "wb.mm"
include "anifp.mm"
include "pm4.72.mm"
include "mpbi.mm"
include "bitr4i.mm"

theorem bj-consensusALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( if- ( ph , ps , ch ) \/ ( ps /\ ch ) ) <-> if- ( ph , ps , ch ) )

  proof
    wph
    wps
    wch
    wif
    #
    wps
    wch
    wa
    #
    wo
    @1
    @0
    wo
    #
    @0
    @0
    @1
    orcom
    @1
    @0
    wi
    @0
    @2
    wb
    wph
    wps
    wch
    anifp
    @1
    @0
    pm4.72
    mpbi
    bitr4i
end
