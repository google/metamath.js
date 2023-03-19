include "wa.mm"
include "simpld.mm"
include "simprd.mm"

theorem simplrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simplrd.1: |- ( ph -> ( ( ps /\ ch ) /\ th ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wa
    wth
    simplrd.1
    simpld
    simprd
end
