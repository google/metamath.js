include "biimpd.mm"
include "imp.mm"

theorem biimpa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biimpa.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    biimpa.1
    biimpd
    imp
end
