include "wa.mm"
include "wo.mm"
include "simpld.mm"
include "adantr.mm"
include "simpr.mm"
include "jca.mm"
include "orcd.mm"
include "olcd.mm"
include "simprd.mm"
include "mpjaodan.mm"

theorem ex-natded9.20
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded9.20.1: |- ( ph -> ( ps /\ ( ch \/ th ) ) )


  assert |- ( ph -> ( ( ps /\ ch ) \/ ( ps /\ th ) ) )

  proof
    wph
    wch
    wps
    wch
    wa
    #
    wps
    wth
    wa
    #
    wo
    wth
    wph
    wch
    wa
    #
    @0
    @1
    @2
    wps
    wch
    wph
    wps
    wch
    wph
    wps
    wch
    wth
    wo
    #
    ex-natded9.20.1
    simpld
    #
    adantr
    wph
    wch
    simpr
    jca
    orcd
    wph
    wth
    wa
    #
    @1
    @0
    @5
    wps
    wth
    wph
    wps
    wth
    @4
    adantr
    wph
    wth
    simpr
    jca
    olcd
    wph
    wps
    @3
    ex-natded9.20.1
    simprd
    mpjaodan
end
