include "wi.mm"
include "jarr.mm"
include "a2d.mm"
include "com12.mm"
include "a1i.mm"

theorem minimp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ph -> ( ( ps -> ch ) -> ( ( ( th -> ps ) -> ( ch -> ta ) ) -> ( ps -> ta ) ) ) )

  proof
    wps
    wch
    wi
    #
    wth
    wps
    wi
    wch
    wta
    wi
    #
    wi
    #
    wps
    wta
    wi
    #
    wi
    wi
    wph
    @2
    @0
    @3
    @2
    wps
    wch
    wta
    wth
    wps
    @1
    jarr
    a2d
    com12
    a1i
end
