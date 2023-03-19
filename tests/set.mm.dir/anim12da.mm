include "anim12dan.mm"

theorem anim12da
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume anim12da.1: |- ( ( ph /\ ps ) -> th )
  assume anim12da.2: |- ( ( ph /\ ch ) -> ta )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> ( th /\ ta ) )

  proof
    wph
    wps
    wth
    wch
    wta
    anim12da.1
    anim12da.2
    anim12dan
end
