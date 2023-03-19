include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "pm2.45.mm"
include "imnan.mm"
include "mpbi.mm"
include "biorfi.mm"
include "orcom.mm"
include "ordir.mm"
include "bitri.mm"
include "pm4.45.mm"
include "anor.mm"
include "orbi2i.mm"
include "anbi2i.mm"
include "3bitrri.mm"

theorem dn1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/ -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch )

  proof
    wch
    wph
    wps
    wo
    wn
    #
    wch
    wo
    #
    wph
    wch
    wo
    #
    wa
    #
    @1
    wph
    wch
    wn
    wch
    wth
    wo
    #
    wn
    wo
    wn
    #
    wo
    #
    wa
    @1
    wn
    @6
    wn
    wo
    wn
    wch
    wch
    @0
    wph
    wa
    #
    wo
    #
    @3
    @7
    wch
    @0
    wph
    wn
    wi
    @7
    wn
    wph
    wps
    pm2.45
    @0
    wph
    imnan
    mpbi
    biorfi
    @8
    @7
    wch
    wo
    @3
    wch
    @7
    orcom
    @0
    wph
    wch
    ordir
    bitri
    bitri
    @2
    @6
    @1
    wch
    @5
    wph
    wch
    wch
    @4
    wa
    @5
    wch
    wth
    pm4.45
    wch
    @4
    anor
    bitri
    orbi2i
    anbi2i
    @1
    @6
    anor
    3bitrri
end
