include "wo.mm"
include "wb.mm"
include "wxo.mm"
include "wn.mm"
include "tsbi2.mm"
include "xnor.mm"
include "orbi2i.mm"
include "sylib.mm"

theorem tsxo2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( ph \/ ps ) \/ -. ( ph \/_ ps ) ) )

  proof
    wth
    wph
    wps
    wo
    #
    wph
    wps
    wb
    #
    wo
    @0
    wph
    wps
    wxo
    wn
    #
    wo
    wph
    wps
    wth
    tsbi2
    @1
    @2
    @0
    wph
    wps
    xnor
    orbi2i
    sylib
end
