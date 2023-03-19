include "wi.mm"
include "wa.mm"
include "ibar.mm"
include "imbi2d.mm"
include "pm5.74i.mm"

theorem pm5.42
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) <-> ( ph -> ( ps -> ( ph /\ ch ) ) ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wph
    wch
    wa
    #
    wi
    wph
    wch
    @0
    wps
    wph
    wch
    ibar
    imbi2d
    pm5.74i
end
