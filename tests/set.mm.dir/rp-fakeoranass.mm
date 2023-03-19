include "wi.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "rp-fakeanorass.mm"
include "bicom.mm"
include "ancom.mm"
include "orcom.mm"
include "anbi1i.mm"
include "bitri.mm"
include "orbi2i.mm"
include "bibi12i.mm"

theorem rp-fakeoranass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ch ) <-> ( ( ( ph \/ ps ) /\ ch ) <-> ( ph \/ ( ps /\ ch ) ) ) )

  proof
    wph
    wch
    wi
    wch
    wps
    wa
    #
    wph
    wo
    #
    wch
    wps
    wph
    wo
    #
    wa
    #
    wb
    #
    wph
    wps
    wo
    #
    wch
    wa
    #
    wph
    wps
    wch
    wa
    #
    wo
    #
    wb
    #
    wch
    wps
    wph
    rp-fakeanorass
    @4
    @3
    @1
    wb
    @9
    @1
    @3
    bicom
    @3
    @6
    @1
    @8
    @3
    @2
    wch
    wa
    @6
    wch
    @2
    ancom
    @2
    @5
    wch
    wps
    wph
    orcom
    anbi1i
    bitri
    @1
    wph
    @0
    wo
    @8
    @0
    wph
    orcom
    @0
    @7
    wph
    wch
    wps
    ancom
    orbi2i
    bitri
    bibi12i
    bitri
    bitri
end
