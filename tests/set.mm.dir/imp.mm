include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "impi.mm"
include "sylbi.mm"

theorem imp
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume imp.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    wph
    wps
    wn
    wi
    wn
    wch
    wph
    wps
    df-an
    wph
    wps
    wch
    imp.1
    impi
    sylbi
end
