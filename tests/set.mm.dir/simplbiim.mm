include "simprbi.mm"
include "syl.mm"

theorem simplbiim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simplbiim.1: |- ( ph <-> ( ps /\ ch ) )
  assume simplbiim.2: |- ( ch -> th )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    simplbiim.1
    simprbi
    simplbiim.2
    syl
end
