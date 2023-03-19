include "wi.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "bitrd.mm"

theorem imbi12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume imbi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume imbi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) )

  proof
    wph
    wps
    wth
    wi
    wch
    wth
    wi
    wch
    wta
    wi
    wph
    wps
    wch
    wth
    imbi12d.1
    imbi1d
    wph
    wth
    wta
    wch
    imbi12d.2
    imbi2d
    bitrd
end
