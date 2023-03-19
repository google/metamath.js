include "wn.mm"
include "wo.mm"
include "wa.mm"
include "exmid.mm"
include "biantrur.mm"
include "andir.mm"
include "pm5.32i.mm"
include "orbi12i.mm"
include "3bitri.mm"

theorem cases
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume cases.1: |- ( ph -> ( ps <-> ch ) )
  assume cases.2: |- ( -. ph -> ( ps <-> th ) )


  assert |- ( ps <-> ( ( ph /\ ch ) \/ ( -. ph /\ th ) ) )

  proof
    wps
    wph
    wph
    wn
    #
    wo
    #
    wps
    wa
    wph
    wps
    wa
    #
    @0
    wps
    wa
    #
    wo
    wph
    wch
    wa
    #
    @0
    wth
    wa
    #
    wo
    @1
    wps
    wph
    exmid
    biantrur
    wph
    @0
    wps
    andir
    @2
    @4
    @3
    @5
    wph
    wps
    wch
    cases.1
    pm5.32i
    @0
    wps
    wth
    cases.2
    pm5.32i
    orbi12i
    3bitri
end
