include "wa.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "wi.mm"
include "orcom.mm"
include "bj-dfbi4.mm"
include "imor.mm"
include "3bitr4i.mm"

theorem bj-dfbi5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph \/ ps ) -> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wa
    #
    wph
    wps
    wo
    #
    wn
    #
    wo
    @2
    @0
    wo
    wph
    wps
    wb
    @1
    @0
    wi
    @0
    @2
    orcom
    wph
    wps
    bj-dfbi4
    @1
    @0
    imor
    3bitr4i
end
