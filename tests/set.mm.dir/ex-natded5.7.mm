include "wo.mm"
include "wa.mm"
include "simpr.mm"
include "orcd.mm"
include "simpld.mm"
include "olcd.mm"
include "mpjaodan.mm"

theorem ex-natded5.7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded5.7.1: |- ( ph -> ( ps \/ ( ch /\ th ) ) )


  assert |- ( ph -> ( ps \/ ch ) )

  proof
    wph
    wps
    wps
    wch
    wo
    wch
    wth
    wa
    #
    wph
    wps
    wa
    wps
    wch
    wph
    wps
    simpr
    orcd
    wph
    @0
    wa
    #
    wch
    wps
    @1
    wch
    wth
    wph
    @0
    simpr
    simpld
    olcd
    ex-natded5.7.1
    mpjaodan
end
