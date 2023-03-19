include "syl.mm"
include "jca.mm"

theorem jccir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jccir.1: |- ( ph -> ps )
  assume jccir.2: |- ( ps -> ch )


  assert |- ( ph -> ( ps /\ ch ) )

  proof
    wph
    wps
    wch
    jccir.1
    wph
    wps
    wch
    jccir.1
    jccir.2
    syl
    jca
end
