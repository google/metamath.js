include "mpd.mm"
include "jca.mm"

theorem jcai
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jcai.1: |- ( ph -> ps )
  assume jcai.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps /\ ch ) )

  proof
    wph
    wps
    wch
    jcai.1
    wph
    wps
    wch
    jcai.1
    jcai.2
    mpd
    jca
end
