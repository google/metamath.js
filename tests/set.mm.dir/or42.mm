include "wo.mm"
include "or4.mm"
include "orcom.mm"
include "orbi2i.mm"
include "bitri.mm"

theorem or42
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( th \/ ps ) ) )

  proof
    wph
    wps
    wo
    wch
    wth
    wo
    wo
    wph
    wch
    wo
    #
    wps
    wth
    wo
    #
    wo
    @0
    wth
    wps
    wo
    #
    wo
    wph
    wps
    wch
    wth
    or4
    @1
    @2
    @0
    wps
    wth
    orcom
    orbi2i
    bitri
end
