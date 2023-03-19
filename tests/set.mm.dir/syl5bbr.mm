include "bicomi.mm"
include "syl5bb.mm"

theorem syl5bbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
