include "id.mm"
include "syl5ibrcom.mm"

theorem biimprcd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biimpcd.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ch -> ( ph -> ps ) )

  proof
    wch
    wps
    wph
    wch
    wch
    id
    biimpcd.1
    syl5ibrcom
end
