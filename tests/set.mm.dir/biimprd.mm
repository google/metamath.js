include "id.mm"
include "syl5ibr.mm"

theorem biimprd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
