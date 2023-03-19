include "wi.mm"
include "pm5.74i.mm"
include "bitri.mm"
include "pm5.74ri.mm"

theorem bitrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bitrd.1: |- ( ph -> ( ps <-> ch ) )
  assume bitrd.2: |- ( ph -> ( ch <-> th ) )


  assert |- ( ph -> ( ps <-> th ) )

  proof
    wph
    wps
    wth
    wph
    wps
    wi
    wph
    wch
    wi
    wph
    wth
    wi
    wph
    wps
    wch
    bitrd.1
    pm5.74i
    wph
    wch
    wth
    bitrd.2
    pm5.74i
    bitri
    pm5.74ri
end
