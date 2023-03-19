include "wa.mm"
include "wi.mm"
include "expd.mm"
include "imdistand.mm"
include "imp.mm"
include "embantd.mm"
include "ex.mm"
include "com23.mm"

theorem a2and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wrh: wff rh
  assume a2and.1: |- ( ph -> ( ( ps /\ rh ) -> ( ta -> th ) ) )
  assume a2and.2: |- ( ph -> ( ( ps /\ rh ) -> ch ) )


  assert |- ( ph -> ( ( ( ps /\ ch ) -> ta ) -> ( ( ps /\ rh ) -> th ) ) )

  proof
    wph
    wps
    wrh
    wa
    #
    wps
    wch
    wa
    #
    wta
    wi
    #
    wth
    wph
    @0
    @2
    wth
    wi
    wph
    @0
    wa
    @1
    wta
    wth
    wph
    @0
    @1
    wph
    wps
    wrh
    wch
    wph
    wps
    wrh
    wch
    a2and.2
    expd
    imdistand
    imp
    wph
    @0
    wta
    wth
    wi
    a2and.1
    imp
    embantd
    ex
    com23
end
