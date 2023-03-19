include "wi.mm"
include "wa.mm"
include "pm5.1.mm"
include "pm5.74rd.mm"

theorem pm5.35
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps <-> ch ) ) )

  proof
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wa
    wph
    wps
    wch
    @0
    @1
    pm5.1
    pm5.74rd
end
