include "wn.mm"
include "wo.mm"
include "wb.mm"
include "wxo.mm"
include "tsbi4.mm"
include "df-xor.mm"
include "bicomi.mm"
include "orbi2i.mm"
include "sylib.mm"

theorem tsxo4
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ ps ) \/ ( ph \/_ ps ) ) )

  proof
    wth
    wph
    wn
    wps
    wo
    #
    wph
    wps
    wb
    wn
    #
    wo
    @0
    wph
    wps
    wxo
    #
    wo
    wph
    wps
    wth
    tsbi4
    @1
    @2
    @0
    @2
    @1
    wph
    wps
    df-xor
    bicomi
    orbi2i
    sylib
end
