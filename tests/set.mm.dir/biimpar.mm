include "biimprd.mm"
include "imp.mm"

theorem biimpar
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume biimpa.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ( ph /\ ch ) -> ps )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    biimpa.1
    biimprd
    imp
end
