include "wb.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "dfbi3.mm"
include "pm4.56.mm"
include "orbi2i.mm"
include "bitri.mm"

theorem bj-dfbi4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ -. ( ph \/ ps ) ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wa
    #
    wph
    wn
    wps
    wn
    wa
    #
    wo
    @0
    wph
    wps
    wo
    wn
    #
    wo
    wph
    wps
    dfbi3
    @1
    @2
    @0
    wph
    wps
    pm4.56
    orbi2i
    bitri
end
