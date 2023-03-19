include "biimpcd.mm"
include "imp.mm"

theorem biimpac
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biimpa.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ( ps /\ ph ) -> ch )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    biimpa.1
    biimpcd
    imp
end
