include "wn.mm"
include "wo.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6rbb.mm"
include "pm5.32ri.mm"

theorem pm5.61
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) )

  proof
    wps
    wn
    #
    wph
    wps
    wo
    #
    wph
    @0
    wph
    wps
    wph
    wo
    @1
    wps
    wph
    biorf
    wps
    wph
    orcom
    syl6rbb
    pm5.32ri
end
