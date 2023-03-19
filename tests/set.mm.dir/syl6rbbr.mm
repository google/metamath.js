include "bicomi.mm"
include "syl6rbb.mm"

theorem syl6rbbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl6rbbr.1: |- ( ph -> ( ps <-> ch ) )
  assume syl6rbbr.2: |- ( th <-> ch )


  assert |- ( ph -> ( th <-> ps ) )

  proof
    wph
    wps
    wch
    wth
    syl6rbbr.1
    wth
    wch
    syl6rbbr.2
    bicomi
    syl6rbb
end
