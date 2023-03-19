include "wn.mm"
include "wi.mm"
include "wo.mm"
include "imdi.mm"
include "df-or.mm"
include "imbi12i.mm"
include "3bitr4i.mm"

theorem orimdi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )

  proof
    wph
    wn
    #
    wps
    wch
    wi
    #
    wi
    @0
    wps
    wi
    #
    @0
    wch
    wi
    #
    wi
    wph
    @1
    wo
    wph
    wps
    wo
    #
    wph
    wch
    wo
    #
    wi
    @0
    wps
    wch
    imdi
    wph
    @1
    df-or
    @4
    @2
    @5
    @3
    wph
    wps
    df-or
    wph
    wch
    df-or
    imbi12i
    3bitr4i
end
