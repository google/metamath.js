include "wn.mm"
include "wo.mm"
include "wb.mm"
include "wxo.mm"
include "tsbi1.mm"
include "xnor.mm"
include "orbi2i.mm"
include "sylib.mm"

theorem tsxo1
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ -. ps ) \/ -. ( ph \/_ ps ) ) )

  proof
    wth
    wph
    wn
    wps
    wn
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
    tsbi1
    @1
    @2
    @0
    wph
    wps
    xnor
    orbi2i
    sylib
end
