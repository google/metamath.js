include "wb.mm"
include "biimpi.mm"
include "biimpa.mm"

theorem bi2imp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bi2imp.1: |- ( ph <-> ( ps <-> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wb
    bi2imp.1
    biimpi
    biimpa
end
