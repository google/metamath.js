include "wa.mm"
include "adantl.mm"
include "sylbi.mm"

theorem simplbiimOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simplbiim.1: |- ( ph <-> ( ps /\ ch ) )
  assume simplbiim.2: |- ( ch -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wa
    wth
    simplbiim.1
    wch
    wth
    wps
    simplbiim.2
    adantl
    sylbi
end
