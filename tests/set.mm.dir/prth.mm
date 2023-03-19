include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "anim12d.mm"

theorem prth
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) -> ( ( ph /\ ch ) -> ( ps /\ th ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wth
    wi
    #
    wa
    wph
    wps
    wch
    wth
    @0
    @1
    simpl
    @0
    @1
    simpr
    anim12d
end
