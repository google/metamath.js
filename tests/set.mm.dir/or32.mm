include "wo.mm"
include "orass.mm"
include "or12.mm"
include "orcom.mm"
include "3bitri.mm"

theorem or32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) )

  proof
    wph
    wps
    wo
    wch
    wo
    wph
    wps
    wch
    wo
    wo
    wps
    wph
    wch
    wo
    #
    wo
    @0
    wps
    wo
    wph
    wps
    wch
    orass
    wph
    wps
    wch
    or12
    wps
    @0
    orcom
    3bitri
end
