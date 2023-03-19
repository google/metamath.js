include "wn.mm"
include "wi.mm"
include "wa.mm"
include "df-an.mm"
include "sylbir.mm"
include "expi.mm"

theorem ex
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ex.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wn
    wi
    wn
    wph
    wps
    wa
    wch
    wph
    wps
    df-an
    ex.1
    sylbir
    expi
end
