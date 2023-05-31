include "bicomi.mm"
include "syl5bb.mm"

theorem syl5bbr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl5bbr.1: |- ( ps <-> ph )
  assume syl5bbr.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ch -> ( ph <-> th ) )

  proof
    wph
    wps
    wch
    wth
    wps
    wph
    syl5bbr.1
    bicomi
    syl5bbr.2
    syl5bb
end
