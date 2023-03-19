include "wa.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem anbi12d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume bi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume bi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) )

  proof
    wph
    wps
    wth
    wa
    wch
    wth
    wa
    wch
    wta
    wa
    wph
    wps
    wch
    wth
    bi12d.1
    anbi1d
    wph
    wth
    wta
    wch
    bi12d.2
    anbi2d
    bitrd
end
