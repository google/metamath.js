include "wi.mm"
include "id.mm"
include "impd.mm"

theorem pm3.31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    wph
    wps
    wch
    @0
    id
    impd
end
