include "id.mm"
include "jctird.mm"

theorem anc2ri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anc2ri.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( ch /\ ph ) ) )

  proof
    wph
    wps
    wch
    wph
    anc2ri.1
    wph
    id
    jctird
end
