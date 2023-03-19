include "wn.mm"
include "wo.mm"
include "wb.mm"
include "wa.mm"
include "pm5.1.mm"
include "olcd.mm"
include "pm3.13.mm"
include "orcd.mm"
include "pm2.61i.mm"
include "a1i.mm"

theorem tsbi1
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ -. ps ) \/ ( ph <-> ps ) ) )

  proof
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
    #
    wth
    wph
    wps
    wa
    #
    @2
    @3
    @1
    @0
    wph
    wps
    pm5.1
    olcd
    @3
    wn
    @0
    @1
    wph
    wps
    pm3.13
    orcd
    pm2.61i
    a1i
end
