include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "df-an.mm"
include "pm4.66.mm"
include "xchbinx.mm"

theorem pm4.54
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) )

  proof
    wph
    wn
    #
    wps
    wa
    @0
    wps
    wn
    #
    wi
    wph
    @1
    wo
    @0
    wps
    df-an
    wph
    wps
    pm4.66
    xchbinx
end
