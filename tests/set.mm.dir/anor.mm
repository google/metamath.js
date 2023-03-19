include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ianor.mm"
include "bicomi.mm"
include "con2bii.mm"

theorem anor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) )

  proof
    wph
    wn
    wps
    wn
    wo
    #
    wph
    wps
    wa
    #
    @1
    wn
    @0
    wph
    wps
    ianor
    bicomi
    con2bii
end
