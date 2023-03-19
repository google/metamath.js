include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "wi.mm"
include "iman.mm"
include "anbi12i.mm"
include "dfbi2.mm"
include "ioran.mm"
include "3bitr4ri.mm"
include "con1bii.mm"

theorem xor
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph <-> ps ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) )

  proof
    wph
    wps
    wn
    wa
    #
    wps
    wph
    wn
    wa
    #
    wo
    #
    wph
    wps
    wb
    #
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
    wn
    #
    @1
    wn
    #
    wa
    @3
    @2
    wn
    @4
    @6
    @5
    @7
    wph
    wps
    iman
    wps
    wph
    iman
    anbi12i
    wph
    wps
    dfbi2
    @0
    @1
    ioran
    3bitr4ri
    con1bii
end
