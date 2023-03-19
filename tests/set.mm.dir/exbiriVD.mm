include "wi.mm"
include "wb.mm"
include "idn3.mm"
include "idn2.mm"
include "wa.mm"
include "idn1.mm"
include "pm3.3.mm"
include "com12.mm"
include "e10.mm"
include "pm2.27.mm"
include "e21.mm"
include "biimpr.mm"
include "e32.mm"
include "in3.mm"
include "in2.mm"
include "in1.mm"

theorem exbiriVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume exbiriVD.1: |- ( ( ph /\ ps ) -> ( ch <-> th ) )


  assert |- ( ph -> ( ps -> ( th -> ch ) ) )

  proof
    wph
    wps
    wth
    wch
    wi
    #
    wi
    wph
    wps
    @0
    wph
    wps
    wth
    wch
    wph
    wps
    wth
    wth
    wch
    wth
    wb
    #
    wch
    wph
    wps
    wth
    idn3
    wph
    wps
    wps
    wps
    @1
    wi
    #
    @1
    wph
    wps
    idn2
    wph
    wph
    wph
    wps
    wa
    @1
    wi
    #
    @2
    wph
    idn1
    exbiriVD.1
    @3
    wph
    @2
    wph
    wps
    @1
    pm3.3
    com12
    e10
    wps
    @1
    pm2.27
    e21
    @1
    wth
    wch
    wch
    wth
    biimpr
    com12
    e32
    in3
    in2
    in1
end
