include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wb.mm"
include "imor.mm"
include "rb-bijust.mm"
include "mpbi.mm"

theorem rb-imdf
  let wph: wff ph
  let wps: wff ps


  assert |- -. ( -. ( -. ( ph -> ps ) \/ ( -. ph \/ ps ) ) \/ -. ( -. ( -. ph \/ ps ) \/ ( ph -> ps ) ) )

  proof
    wph
    wps
    wi
    #
    wph
    wn
    wps
    wo
    #
    wb
    @0
    wn
    @1
    wo
    wn
    @1
    wn
    @0
    wo
    wn
    wo
    wn
    wph
    wps
    imor
    @0
    @1
    rb-bijust
    mpbi
end
