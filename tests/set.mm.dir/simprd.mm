include "ancomd.mm"
include "simpld.mm"

theorem simprd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume simprd.1: |- ( ph -> ( ps /\ ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    simprd.1
    ancomd
    simpld
end
