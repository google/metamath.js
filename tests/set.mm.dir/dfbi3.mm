include "wi.mm"
include "wa.mm"
include "wn.mm"
include "wb.mm"
include "wo.mm"
include "con34b.mm"
include "anbi2i.mm"
include "dfbi2.mm"
include "cases2.mm"
include "3bitr4i.mm"

theorem dfbi3
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) )

  proof
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wa
    @0
    wph
    wn
    #
    wps
    wn
    #
    wi
    #
    wa
    wph
    wps
    wb
    wph
    wps
    wa
    @2
    @3
    wa
    wo
    @1
    @4
    @0
    wps
    wph
    con34b
    anbi2i
    wph
    wps
    dfbi2
    wph
    wps
    @3
    cases2
    3bitr4i
end
