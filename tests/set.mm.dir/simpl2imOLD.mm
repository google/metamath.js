include "wa.mm"
include "simpr.mm"
include "3syl.mm"

theorem simpl2imOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simpl2im.1: |- ( ph -> ( ps /\ ch ) )
  assume simpl2im.2: |- ( ch -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wa
    wch
    wth
    simpl2im.1
    wps
    wch
    simpr
    simpl2im.2
    3syl
end
