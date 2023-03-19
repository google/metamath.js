include "biimprd.mm"
include "imp.mm"

theorem biimpar
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
