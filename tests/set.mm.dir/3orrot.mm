include "wo.mm"
include "w3o.mm"
include "orcom.mm"
include "3orass.mm"
include "df-3or.mm"
include "3bitr4i.mm"

theorem 3orrot
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) )

  proof
    wph
    wps
    wch
    wo
    #
    wo
    @0
    wph
    wo
    wph
    wps
    wch
    w3o
    wps
    wch
    wph
    w3o
    wph
    @0
    orcom
    wph
    wps
    wch
    3orass
    wps
    wch
    wph
    df-3or
    3bitr4i
end
