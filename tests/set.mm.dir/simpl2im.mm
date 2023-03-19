include "simprd.mm"
include "syl.mm"

theorem simpl2im
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simpl2im.1: |- ( ph -> ( ps /\ ch ) )
  assume simpl2im.2: |- ( ch -> th )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    simpl2im.1
    simprd
    simpl2im.2
    syl
end
