include "wb.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "orbi12d.mm"

theorem pm4.39
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) -> ( ( ph \/ ps ) <-> ( ch \/ th ) ) )

  proof
    wph
    wch
    wb
    #
    wps
    wth
    wb
    #
    wa
    wph
    wch
    wps
    wth
    @0
    @1
    simpl
    @0
    @1
    simpr
    orbi12d
end
