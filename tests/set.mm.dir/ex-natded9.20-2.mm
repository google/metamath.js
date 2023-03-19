include "wa.mm"
include "wo.mm"
include "simpld.mm"
include "anim1i.mm"
include "orcd.mm"
include "olcd.mm"
include "simprd.mm"
include "mpjaodan.mm"

theorem ex-natded9.20-2
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
    @0
    @1
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
    anim1i
    orcd
    wph
    wth
    wa
    @1
    @0
    wph
    wps
    wth
    @3
    anim1i
    olcd
    wph
    wps
    @2
    ex-natded9.20.1
    simprd
    mpjaodan
end
