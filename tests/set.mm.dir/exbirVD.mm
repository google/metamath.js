include "wa.mm"
include "wb.mm"
include "wi.mm"
include "idn3.mm"
include "idn1.mm"
include "idn2.mm"
include "id.mm"
include "e12.mm"
include "biimpr.mm"
include "com12.mm"
include "e32.mm"
include "in3.mm"
include "in2.mm"
include "pm3.3.mm"
include "e1a.mm"
include "in1.mm"

theorem exbirVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ph -> ( ps -> ( th -> ch ) ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wth
    wb
    #
    wi
    #
    wph
    wps
    wth
    wch
    wi
    #
    wi
    wi
    #
    @2
    @0
    @3
    wi
    @4
    @2
    @0
    @3
    @2
    @0
    wth
    wch
    @2
    @0
    wth
    wth
    @1
    wch
    @2
    @0
    wth
    idn3
    @2
    @2
    @0
    @0
    @1
    @2
    idn1
    @2
    @0
    idn2
    @2
    id
    e12
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
    wph
    wps
    @3
    pm3.3
    e1a
    in1
end
