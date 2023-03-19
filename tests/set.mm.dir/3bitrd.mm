include "bitrd.mm"

theorem 3bitrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitrd.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitrd.2: |- ( ph -> ( ch <-> th ) )
  assume 3bitrd.3: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ps <-> ta ) )

  proof
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    3bitrd.1
    3bitrd.2
    bitrd
    3bitrd.3
    bitrd
end
