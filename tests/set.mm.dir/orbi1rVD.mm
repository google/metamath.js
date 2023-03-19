include "wb.mm"
include "wo.mm"
include "wi.mm"
include "idn1.mm"
include "idn2.mm"
include "pm1.4.mm"
include "e2.mm"
include "orbi1.mm"
include "biimpd.mm"
include "e12.mm"
include "in2.mm"
include "biimprd.mm"
include "impbi.mm"
include "e11.mm"
include "in1.mm"

theorem orbi1rVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wph
    wo
    #
    wch
    wps
    wo
    #
    wb
    #
    @0
    @1
    @2
    wi
    @2
    @1
    wi
    @3
    @0
    @1
    @2
    @0
    @1
    wps
    wch
    wo
    #
    @2
    @0
    @0
    @1
    wph
    wch
    wo
    #
    @4
    @0
    idn1
    #
    @0
    @1
    @1
    @5
    @0
    @1
    idn2
    wch
    wph
    pm1.4
    e2
    @0
    @5
    @4
    wph
    wps
    wch
    orbi1
    #
    biimpd
    e12
    wps
    wch
    pm1.4
    e2
    in2
    @0
    @2
    @1
    @0
    @2
    @5
    @1
    @0
    @0
    @2
    @4
    @5
    @6
    @0
    @2
    @2
    @4
    @0
    @2
    idn2
    wch
    wps
    pm1.4
    e2
    @0
    @5
    @4
    @7
    biimprd
    e12
    wph
    wch
    pm1.4
    e2
    in2
    @1
    @2
    impbi
    e11
    in1
end
