include "bj-0.mm"
include "id.mm"

theorem bj-1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( ( ph -> ps ) -> ch ) )

  proof
    wph
    wps
    wch
    bj-0
    id
end
