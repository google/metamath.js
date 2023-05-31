include "ancomd.mm"
include "simpld.mm"

theorem simprd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
