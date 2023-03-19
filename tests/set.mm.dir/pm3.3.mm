include "wa.mm"
include "wi.mm"
include "id.mm"
include "expd.mm"

theorem pm3.3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wa
    wch
    wi
    #
    wph
    wps
    wch
    @0
    id
    expd
end
