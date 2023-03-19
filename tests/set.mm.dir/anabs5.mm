include "wa.mm"
include "ibar.mm"
include "bicomd.mm"
include "pm5.32i.mm"

theorem anabs5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) )

  proof
    wph
    wph
    wps
    wa
    #
    wps
    wph
    wps
    @0
    wph
    wps
    ibar
    bicomd
    pm5.32i
end
