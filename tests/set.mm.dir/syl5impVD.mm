include "wi.mm"
include "idn2.mm"
include "idn1.mm"
include "pm2.04.mm"
include "e1a.mm"
include "imim1.mm"
include "e21.mm"
include "e2.mm"
include "in2.mm"
include "in1.mm"

theorem syl5impVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( th -> ps ) -> ( ph -> ( th -> ch ) ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    wth
    wps
    wi
    #
    wph
    wth
    wch
    wi
    wi
    #
    wi
    @0
    @1
    @2
    @0
    @1
    wth
    wph
    wch
    wi
    #
    wi
    #
    @2
    @0
    @1
    @1
    wps
    @3
    wi
    #
    @4
    @0
    @1
    idn2
    @0
    @0
    @5
    @0
    idn1
    wph
    wps
    wch
    pm2.04
    e1a
    wth
    wps
    @3
    imim1
    e21
    wth
    wph
    wch
    pm2.04
    e2
    in2
    in1
end
