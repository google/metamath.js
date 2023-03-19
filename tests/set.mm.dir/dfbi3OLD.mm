include "wn.mm"
include "wb.mm"
include "wa.mm"
include "wo.mm"
include "xor.mm"
include "pm5.18.mm"
include "notnotb.mm"
include "anbi2i.mm"
include "ancom.mm"
include "orbi12i.mm"
include "3bitr4i.mm"

theorem dfbi3OLD
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) )

  proof
    wph
    wps
    wn
    #
    wb
    wn
    wph
    @0
    wn
    #
    wa
    #
    @0
    wph
    wn
    #
    wa
    #
    wo
    wph
    wps
    wb
    wph
    wps
    wa
    #
    @3
    @0
    wa
    #
    wo
    wph
    @0
    xor
    wph
    wps
    pm5.18
    @5
    @2
    @6
    @4
    wps
    @1
    wph
    wps
    notnotb
    anbi2i
    @3
    @0
    ancom
    orbi12i
    3bitr4i
end
