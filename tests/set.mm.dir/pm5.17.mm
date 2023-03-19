include "wn.mm"
include "wb.mm"
include "wi.mm"
include "wa.mm"
include "wo.mm"
include "bicom.mm"
include "dfbi2.mm"
include "orcom.mm"
include "df-or.mm"
include "bitr2i.mm"
include "imnan.mm"
include "anbi12i.mm"
include "3bitrri.mm"

theorem pm5.17
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) )

  proof
    wph
    wps
    wn
    #
    wb
    @0
    wph
    wb
    @0
    wph
    wi
    #
    wph
    @0
    wi
    #
    wa
    wph
    wps
    wo
    #
    wph
    wps
    wa
    wn
    #
    wa
    wph
    @0
    bicom
    @0
    wph
    dfbi2
    @1
    @3
    @2
    @4
    @3
    wps
    wph
    wo
    @1
    wph
    wps
    orcom
    wps
    wph
    df-or
    bitr2i
    wph
    wps
    imnan
    anbi12i
    3bitrri
end
