include "wo.mm"
include "wi.mm"
include "wa.mm"
include "jaob.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem pm5.53
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <-> ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) )

  proof
    wph
    wps
    wo
    #
    wch
    wo
    wth
    wi
    @0
    wth
    wi
    #
    wch
    wth
    wi
    #
    wa
    wph
    wth
    wi
    wps
    wth
    wi
    wa
    #
    @2
    wa
    @0
    wth
    wch
    jaob
    @1
    @3
    @2
    wph
    wth
    wps
    jaob
    anbi1i
    bitri
end
