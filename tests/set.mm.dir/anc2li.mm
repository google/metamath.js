include "id.mm"
include "jctild.mm"

theorem anc2li
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anc2li.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    wph
    anc2li.1
    wph
    id
    jctild
end
