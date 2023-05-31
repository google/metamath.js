include "bicomi.mm"
include "syl6bb.mm"

theorem syl6bbr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6bbr.1: |- ( ph -> ( ps <-> ch ) )
  assume syl6bbr.2: |- ( th <-> ch )


  assert |- ( ph -> ( ps <-> th ) )

  proof
    wph
    wps
    wch
    wth
    syl6bbr.1
    wth
    wch
    syl6bbr.2
    bicomi
    syl6bb
end
