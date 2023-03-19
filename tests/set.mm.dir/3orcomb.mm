include "wo.mm"
include "w3o.mm"
include "orcom.mm"
include "orbi2i.mm"
include "3orass.mm"
include "3bitr4i.mm"

theorem 3orcomb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) )

  proof
    wph
    wps
    wch
    wo
    #
    wo
    wph
    wch
    wps
    wo
    #
    wo
    wph
    wps
    wch
    w3o
    wph
    wch
    wps
    w3o
    @0
    @1
    wph
    wps
    wch
    orcom
    orbi2i
    wph
    wps
    wch
    3orass
    wph
    wch
    wps
    3orass
    3bitr4i
end
