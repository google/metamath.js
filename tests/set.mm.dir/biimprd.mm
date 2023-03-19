include "id.mm"
include "syl5ibr.mm"

theorem biimprd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume biimprd.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wch
    wps
    wph
    wch
    wch
    id
    biimprd.1
    syl5ibr
end
