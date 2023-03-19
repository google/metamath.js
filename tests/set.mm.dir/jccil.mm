include "jccir.mm"
include "ancomd.mm"

theorem jccil
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jccir.1: |- ( ph -> ps )
  assume jccir.2: |- ( ps -> ch )


  assert |- ( ph -> ( ch /\ ps ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    jccir.1
    jccir.2
    jccir
    ancomd
end
