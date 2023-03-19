include "ex.mm"
include "wb.mm"
include "wi.mm"
include "a1i.mm"
include "pm5.21ndd.mm"

theorem pm5.21nd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm5.21nd.1: |- ( ( ph /\ ps ) -> th )
  assume pm5.21nd.2: |- ( ( ph /\ ch ) -> th )
  assume pm5.21nd.3: |- ( th -> ( ps <-> ch ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wth
    wps
    wch
    wph
    wps
    wth
    pm5.21nd.1
    ex
    wph
    wch
    wth
    pm5.21nd.2
    ex
    wth
    wps
    wch
    wb
    wi
    wph
    pm5.21nd.3
    a1i
    pm5.21ndd
end
