include "wa.mm"
include "wn.mm"
include "wo.mm"
include "exmid.mm"
include "biantrur.mm"
include "orcom.mm"
include "anbi12i.mm"
include "anass.mm"
include "orddi.mm"
include "3bitr4ri.mm"
include "wl-orel12.mm"
include "pm4.71i.mm"
include "ancom.mm"
include "3bitr2i.mm"

theorem wl-cases2-dnf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) <-> ( ( -. ph \/ ps ) /\ ( ph \/ ch ) ) )

  proof
    wph
    wps
    wa
    wph
    wn
    #
    wch
    wa
    wo
    #
    wph
    wch
    wo
    #
    @0
    wps
    wo
    #
    wa
    #
    wch
    wps
    wo
    #
    wa
    #
    @4
    @3
    @2
    wa
    @2
    @3
    @5
    wa
    #
    wa
    wph
    @0
    wo
    #
    @2
    wa
    #
    wps
    @0
    wo
    #
    wps
    wch
    wo
    #
    wa
    #
    wa
    @6
    @1
    @2
    @9
    @7
    @12
    @8
    @2
    wph
    exmid
    biantrur
    @3
    @10
    @5
    @11
    @0
    wps
    orcom
    wch
    wps
    orcom
    anbi12i
    anbi12i
    @2
    @3
    @5
    anass
    wph
    wps
    @0
    wch
    orddi
    3bitr4ri
    @4
    @5
    wph
    wch
    wps
    wl-orel12
    pm4.71i
    @2
    @3
    ancom
    3bitr2i
end
