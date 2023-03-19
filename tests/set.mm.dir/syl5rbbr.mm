include "bicomi.mm"
include "syl5rbb.mm"

theorem syl5rbbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5rbbr.1: |- ( ps <-> ph )
  assume syl5rbbr.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ch -> ( th <-> ph ) )

  proof
    wph
    wps
    wch
    wth
    wps
    wph
    syl5rbbr.1
    bicomi
    syl5rbbr.2
    syl5rbb
end
