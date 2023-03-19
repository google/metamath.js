include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "dfbi1.mm"
include "imor.mm"
include "notbii.mm"
include "imbi12i.mm"
include "pm4.62.mm"
include "3bitri.mm"

theorem rb-bijust
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wn
    #
    wi
    #
    wn
    wph
    wn
    wps
    wo
    #
    wps
    wn
    wph
    wo
    #
    wn
    #
    wi
    #
    wn
    @4
    wn
    @6
    wo
    #
    wn
    wph
    wps
    dfbi1
    @3
    @7
    @0
    @4
    @2
    @6
    wph
    wps
    imor
    @1
    @5
    wps
    wph
    imor
    notbii
    imbi12i
    notbii
    @7
    @8
    @4
    @5
    pm4.62
    notbii
    3bitri
end
