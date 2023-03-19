include "wo.mm"
include "w3o.mm"
include "or12.mm"
include "3orass.mm"
include "3bitr4i.mm"

theorem 3orcoma
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) )

  proof
    wph
    wps
    wch
    wo
    wo
    wps
    wph
    wch
    wo
    wo
    wph
    wps
    wch
    w3o
    wps
    wph
    wch
    w3o
    wph
    wps
    wch
    or12
    wph
    wps
    wch
    3orass
    wps
    wph
    wch
    3orass
    3bitr4i
end
