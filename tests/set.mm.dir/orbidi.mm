include "wn.mm"
include "wb.mm"
include "wi.mm"
include "wo.mm"
include "pm5.74.mm"
include "df-or.mm"
include "bibi12i.mm"
include "3bitr4i.mm"

theorem orbidi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps <-> ch ) ) <-> ( ( ph \/ ps ) <-> ( ph \/ ch ) ) )

  proof
    wph
    wn
    #
    wps
    wch
    wb
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
    wb
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
    wb
    @0
    wps
    wch
    pm5.74
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
    bibi12i
    3bitr4i
end
