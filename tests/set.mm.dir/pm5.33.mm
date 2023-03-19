include "wi.mm"
include "wa.mm"
include "ibar.mm"
include "imbi1d.mm"
include "pm5.32i.mm"

theorem pm5.33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps -> ch ) ) <-> ( ph /\ ( ( ph /\ ps ) -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wph
    wps
    wa
    #
    wch
    wi
    wph
    wps
    @0
    wch
    wph
    wps
    ibar
    imbi1d
    pm5.32i
end
