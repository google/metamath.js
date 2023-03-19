include "id.mm"
include "syl5com.mm"

theorem com12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume com12.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ps -> ( ph -> ch ) )

  proof
    wps
    wps
    wph
    wch
    wps
    id
    com12.1
    syl5com
end
