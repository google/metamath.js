include "wn.mm"
include "wo.mm"
include "wb.mm"
include "tsbi3.mm"
include "orcom.mm"
include "bicom.mm"
include "notbii.mm"
include "orbi12i.mm"
include "sylib.mm"

theorem tsbi4
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ ps ) \/ -. ( ph <-> ps ) ) )

  proof
    wth
    wps
    wph
    wn
    #
    wo
    #
    wps
    wph
    wb
    #
    wn
    #
    wo
    @0
    wps
    wo
    #
    wph
    wps
    wb
    #
    wn
    #
    wo
    wps
    wph
    wth
    tsbi3
    @1
    @4
    @3
    @6
    wps
    @0
    orcom
    @2
    @5
    wps
    wph
    bicom
    notbii
    orbi12i
    sylib
end
