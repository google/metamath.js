include "wo.mm"
include "orcom.mm"
include "or12.mm"
include "orbi2i.mm"
include "3bitri.mm"

theorem orass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) )

  proof
    wph
    wps
    wo
    #
    wch
    wo
    wch
    @0
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
    wo
    #
    wo
    @0
    wch
    orcom
    wch
    wph
    wps
    or12
    @1
    @2
    wph
    wch
    wps
    orcom
    orbi2i
    3bitri
end
