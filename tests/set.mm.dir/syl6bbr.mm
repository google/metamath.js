include "bicomi.mm"
include "syl6bb.mm"

theorem syl6bbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
