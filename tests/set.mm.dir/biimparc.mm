include "biimprcd.mm"
include "imp.mm"

theorem biimparc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biimpa.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ( ch /\ ph ) -> ps )

  proof
    wch
    wph
    wps
    wph
    wps
    wch
    biimpa.1
    biimprcd
    imp
end
