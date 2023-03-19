include "wo.mm"
include "or12.mm"
include "orbi2i.mm"
include "orass.mm"
include "3bitr4i.mm"

theorem or4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( ps \/ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wo
    #
    wo
    #
    wo
    wph
    wch
    wps
    wth
    wo
    #
    wo
    #
    wo
    wph
    wps
    wo
    @0
    wo
    wph
    wch
    wo
    @2
    wo
    @1
    @3
    wph
    wps
    wch
    wth
    or12
    orbi2i
    wph
    wps
    @0
    orass
    wph
    wch
    @2
    orass
    3bitr4i
end
