include "wb.mm"
include "wi.mm"
include "idn1.mm"
include "idn2.mm"
include "idn3.mm"
include "imbi12.mm"
include "e23.mm"
include "e13.mm"
include "in3.mm"
include "in2.mm"
include "in1.mm"

theorem imbi13VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ta <-> et ) -> ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th -> et ) ) ) ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wta
    wet
    wb
    #
    wph
    wch
    wta
    wi
    #
    wi
    wps
    wth
    wet
    wi
    #
    wi
    wb
    #
    wi
    #
    wi
    @0
    @1
    @6
    @0
    @1
    @2
    @5
    @0
    @0
    @1
    @2
    @3
    @4
    wb
    #
    @5
    @0
    idn1
    @0
    @1
    @1
    @2
    @2
    @7
    @0
    @1
    idn2
    @0
    @1
    @2
    idn3
    wch
    wth
    wta
    wet
    imbi12
    e23
    wph
    wps
    @3
    @4
    imbi12
    e13
    in3
    in2
    in1
end
