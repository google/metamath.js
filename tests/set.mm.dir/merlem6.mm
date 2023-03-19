include "wi.mm"
include "merlem4.mm"
include "merlem3.mm"
include "ax-mp.mm"

theorem merlem6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) )

  proof
    wps
    wch
    wi
    #
    @0
    wph
    wi
    wth
    wph
    wi
    wi
    #
    wi
    wch
    @1
    wi
    wph
    wth
    @0
    merlem4
    @1
    wps
    wch
    merlem3
    ax-mp
end
