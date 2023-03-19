include "wi.mm"
include "id.mm"
include "anim1d.mm"

theorem pm3.45
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wch
    @0
    id
    anim1d
end
